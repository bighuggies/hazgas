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
chan Vent = [0] of {mtype};
chan AgentClock = [0] of {mtype};

bool inited = false;
bool alarming = false;
bool is_reset = false;

int num_ticks_alarming = 0;

/* Message types */
mtype = {
    M_TICK,
    M_VENT,
    M_UNVENT
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
    od;
};

/* Factory controller, which gathers information from individual rooms, and alarms if appropriate */
proctype FactoryController(chan Vent_in,
                                AgentClock_out) {
    /* Number of venting rooms */
    int venting = 0;
    /* Window of previous clock ticks */
    bool window[ALARM_WINDOW];

    do
    ::  atomic {
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
        num_ticks_alarming = 0;
        {
            int i;
            for (i : 0 .. ALARM_WINDOW - 1) {
                num_ticks_alarming = num_ticks_alarming + window[i];
            }
        }

        /* If the number of recent venting ticks is >threshold, alarm. */
        alarming = alarming || num_ticks_alarming >= ALARM_THRESHOLD;

        AgentClock_out ! M_TICK;
    od;
};

/* The agent that resets the alarm */
proctype Agent(chan AgentClock_in) {
    /* Reset alarm */
    do
    :: AgentClock_in ? M_TICK ->
        is_reset = true;

        alarming = false;

        is_reset = false;
    od;
};

Room rooms[NUM_ROOMS];  /* Create rooms */

#   include "claims.ltl"

init {
    /* Initialise rooms */
#   include "rooms.pml"
    inited = true;

    atomic {
        int i;
        for (i : 0 .. NUM_ROOMS - 1) {
            run RoomController(rooms[i], Vent, Clock[i]);
        }
        run FactoryController(Vent, AgentClock);
        run Agent(AgentClock);
    }
}
