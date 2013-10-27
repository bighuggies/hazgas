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
chan Clock[NUM_ROOMS] = [0] of {mtype};
chan Vent = [NUM_ROOMS] of {mtype};
chan Alarm = [0] of {mtype};

bool inited = false;
bool alarming = false;
bool is_reset = false;

/* Message types */
mtype = {
    M_TICK,
    M_VENT,
    M_UNVENT,
    M_ALARM
};

/* Room struct */
typedef Room {
    int i;              /* Room number */
    int volume;         /* Volume of the room in litres */
    int gasVolume;      /* Volume of gas in the room */

    int lowerBound;     /* Threshold to SHUT vent */
    int upperBound;     /* Threshold to OPEN vent */
    int ventRate;       /* Rate at which the gas DECREASES when venting */
    int gasRate;        /* Rate at which the gas INCREASES each clock tick */

    bool venting;       /* Is the room venting? */
};

/* Room controller, which reads room gas concentration, vents or stops venting as appropriate, 
 * and communicates with the factory controller */
proctype RoomController(Room room;
                        chan Vent_out,
                        Clock_in) {
    do
    /* Every tick, increase gas then perform appropriate venting options */
    :: Clock_in ? M_TICK ->
        /* Increase gas volume */
        room.gasVolume = room.gasVolume + room.gasRate;

        /* Check venting status, then output any change */
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

        /* If venting; decrease gas volume */
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

/* Factory controller, which gathers information from individual rooms, and alarms if appropriate */
proctype FactoryController(chan Vent_in,
                                Alarm_out) {
    /* Number of venting rooms */
    int venting = 0;
    /* Window of previous clock ticks */
    bool window[ALARM_WINDOW];

    do
    ::  atomic {
            printf("t\n");
            int i;
            for (i : 0 .. NUM_ROOMS - 1) {
                Clock[i] ! M_TICK;
            }
        }

        if
        /* Increment num of rooms venting */
        :: nempty(Vent_in) ->
            if
            :: Vent_in ? M_VENT ->
                venting++;
            :: Vent_in ? M_UNVENT ->
                venting--;
            fi;

        :: empty(Vent_in) ->
            skip;
        fi;

        /* Move window along */
        atomic {
            int i;
            for (i : 1 .. ALARM_WINDOW - 1) {
                window[ALARM_WINDOW - i] = window[ALARM_WINDOW - i - 1];
            }
        }

        /* If at least one room was venting, set window index to true */
        window[0] = venting > 0;

        /* Calculate the number of ticks in which a room was venting */
        int numTicksAlarming;
        {
            int i;
            for (i : 0 .. ALARM_WINDOW - 1) {
                numTicksAlarming = numTicksAlarming + window[i];
            }
        }

        /* If the number of recent venting ticks is >threshold, alarm. */
        alarming = alarming || numTicksAlarming >= ALARM_THRESHOLD;

        if
        ::  alarming ->
            printf("!\n");
            Alarm_out ! M_ALARM;
        :: else ->
            skip;
        fi;

    od;
};

/* The agent that resets the alarm */
proctype Agent(chan Alarm_in) {
    /* Reset alarm */
    do
    :: Alarm_in ? M_ALARM ->
        is_reset = true;

        alarming = false;

        is_reset = false;
        printf(".\n");
    od;
};

Room rooms[NUM_ROOMS];  /* Create rooms */

#   include "claims.ltl"

init {
    /* Initialise rooms */
#   include "rooms.pml"
    inited = true;

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
        run FactoryController(Vent, Alarm);
        run Agent(Alarm);
    }
}
