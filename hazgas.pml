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

/* Global variables */
chan Clock[NUM_ROOMS]    = [0] of {mtype};
chan Vent = [NUM_ROOMS] of {mtype};
chan Alarm = [0] of {mtype};
chan Reset = [0] of {mtype};

bool alarming = false;

#ifdef UI
chan STDIN;
#endif

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

proctype RoomController(Room room;
                        chan Vent_out,
                        Clock_in) {
    end: do
    :: Clock_in ? M_TICK ->
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
    bool window[ALARM_WINDOW];

    end: do
    ::  atomic {
            int i;
            for (i : 0 .. NUM_ROOMS - 1) {
                Clock[i] ! M_TICK;
            }
        }

        if
           /* If the alarm has been reset; stop alarming */
        :: Reset_in ? M_RESET ->
            alarming = false;
            printf(".\n");

        /* Increment num of rooms venting */
        :: nempty(Vent_in) ->
            if
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
            :: Vent_in ? M_UNVENT ->
                venting--;
            fi;

        :: empty(Vent_in) ->
            skip;
        fi;

        window[0] = venting > 0;
        atomic {
            int i;
            for (i : NUM_ROOMS - 2 .. 0) {
                window[i + 1] = window[i];
            }
        }

        int numTicksAlarming;
        {
            int i;
            for (i : 0 .. ALARM_WINDOW - 1) {
                numTicksAlarming = numTicksAlarming + window[i];
            }
        }
        alarming = alarming || numTicksAlarming > ALARM_THRESHOLD;
    od;
};

proctype Agent(chan Alarm_in,
                    Reset_out) {

    /* Reset alarm */
    end: do
    :: Alarm_in ? M_ALARM ->
#ifdef UI
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
#else
        Reset_out ! M_RESET;
#endif
    od;
};

init {
    Room rooms[NUM_ROOMS];  /* Create rooms */

    /* Initialise rooms */
#   include "rooms.pml"

    atomic {
        printf("%d\n", NUM_ROOMS);

        int i;
        for (i : 0 .. NUM_ROOMS - 1) {
            printf("%d:%d:%d:%d:%d:%d\n", rooms[i].i,
                                          rooms[i].volume,
                                          rooms[i].lowerBound,
                                          rooms[i].upperBound,
                                          rooms[i].ventRate,
                                          rooms[i].gasRate);

            run RoomController(rooms[i], Vent, Clock[i]);
        }
        run FactoryController(Vent, Alarm, Reset);
        run Agent(Alarm, Reset);
    }
}
