/*
 * Hazardous Gas Detection System ("hazgas")
 * Best Group
 *
 * Alexander Borsboom
 * Andrew Hughson
 * Andrew Luey
 * Sam Metson
 * Tony Young
 */

#include "params.pml"

bool alarming = false;

chan STDIN;

/* Message types */
mtype = {
    M_TICK,
    M_VENT,
    M_UNVENT,
    M_ALARM,
    M_RESET
};

/* Room struct */
typedef Room {
    int i;              /* Room number */
    int volume;         /* Volume of the room in litres */
    int gasVolume;      /* Volume of gas in the room */

    int lowerBound;     /* Threshold to SHUT vent */
    int upperBound;     /* Threshold to OPEN vent */
    int ventRate;
    int gasRate;

    bool venting;
};

Room rooms[NUM_ROOMS];  /* Create rooms */

proctype RoomController(Room room;
                        chan Vent_out) {
    end: do
    ::
        /* Increase gas volume */
        room.gasVolume = room.gasVolume + room.gasRate;

        /* Check venting status */
        if
        :: ((room.gasVolume >= room.upperBound) || alarming) &&
           !room.venting ->
            room.venting = true;
            Vent_out ! M_VENT;
        :: (room.gasVolume <= room.lowerBound) && !alarming &&
           room.venting ->
            room.venting = false;
            Vent_out ! M_UNVENT;
        :: else ->
            skip;
        fi;

        /* If venting; decrement gas volume */
        if
        :: room.venting ->
            atomic {
                room.gasVolume = room.gasVolume - room.ventRate;
                if
                :: room.gasVolume < 0 ->
                    room.gasVolume = 0
                :: else ->
                    skip
                fi;
            }
        :: else ->
            skip;
        fi;

        printf("%d:%d:%d\n", room.i, room.gasVolume, room.venting);
    od;
};

proctype FactoryController(chan Vent_in,
                                Alarm_out,
                                Reset_in) {
    int venting = 0;

    end: do
    /* If the alarm has been reset; stop alarming */
    :: Reset_in ? M_RESET ->
        alarming = false;
        printf(".\n");

    /* Increment num of rooms venting */
    :: Vent_in ? M_VENT ->
        venting++;

        /* If the num of rooms alarming is over the threshold; ALARM!!!!! */
        if
        :: venting >= ALARM_THRESHOLD && !alarming ->
            alarming = true;
            printf("!\n");
            Alarm_out ! M_ALARM;
        :: else ->
            skip;
        fi;

    /* Decrement num of rooms venting */
    :: Vent_in ? M_UNVENT ->
        venting--;
    od;
};

proctype Agent(chan Alarm_in,
                    Reset_out) {

    /* Reset alarm */
    end: do
    :: Alarm_in ? M_ALARM ->
        int c;
        do
        :: STDIN ? c ->
            if
            :: c == '.' ->
                Reset_out ! M_RESET;
                break;
            :: else ->
                printf("!\n");
            fi;
        od;
    od;
};

/* Global variables */
chan Vent = [0] of {mtype};
chan Alarm = [0] of {mtype};
chan Reset = [0] of {mtype};

init {
    int c;

    /* Initialise rooms */
    atomic {
        int i;
        for (i : 0 .. NUM_ROOMS - 1) {
            int lowerBound;
            select(lowerBound : LOWER_BOUND_LOW..LOWER_BOUND_HIGH);
            rooms[i].lowerBound = lowerBound;

            int range;
            select(range : UPPER_BOUND_OFFSET_LOW..UPPER_BOUND_OFFSET_HIGH);
            rooms[i].upperBound = lowerBound + range;

            int volume;
            select(volume : VOLUME_LOW..VOLUME_HIGH);
            rooms[i].volume = volume;

            int gasRate;
            select(gasRate : GAS_LOW..GAS_HIGH);
            rooms[i].gasRate = gasRate;

            select(range : VENT_OFFSET_LOW..VENT_OFFSET_HIGH);
            rooms[i].ventRate = gasRate + range;
        }
    }

    atomic {
        int i;
        printf("%d\n", NUM_ROOMS);
        for (i : 0 .. NUM_ROOMS - 1) {
            rooms[i].i = i;
            printf("%d:%d:%d:%d:%d:%d\n", rooms[i].i,
                                          rooms[i].volume,
                                          rooms[i].lowerBound,
                                          rooms[i].upperBound,
                                          rooms[i].ventRate,
                                          rooms[i].gasRate);

            run RoomController(rooms[i], Vent);
        }
        run FactoryController(Vent, Alarm, Reset);
        run Agent(Alarm, Reset);
    }
}
