#define NUM_ROOMS 2
#define ALARM_THRESHOLD 1

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

    chan Clock_in;
    chan Alarm_in;

    int lowerBound;     /* Threshold to SHUT vent */
    int upperBound;     /* Threshold to OPEN vent */
    int ventRate;
    int gasRate;

    bool venting;
    bool alarming;
};

Room rooms[NUM_ROOMS];  /* Create rooms */

proctype RoomController(Room room;
                        chan Vent_out) {
    end: do
    /* If alarming; start venting */
    :: room.Alarm_in ? M_ALARM ->
        printf("Room %d has received an ALARM.\n", room.i);
        room.alarming = true;

        if
        :: !room.venting ->
            Vent_out ! M_VENT;
            room.venting = true;
        :: else ->
            skip;
        fi;

    /* Stop alarming */
    :: room.Alarm_in ? M_RESET ->
        printf("Room %d has STOPPED ALARMING.\n", room.i);
        room.alarming = false;

    /* On each clock tick */
    :: room.Clock_in ? M_TICK ->

        /* Increase gas volume */
        room.gasVolume = room.gasVolume + room.gasRate;

        /* If alarming; vent */
        if
        :: room.alarming ->
            goto ventOnly;
        :: else ->
            skip;
        fi;

        /* Check venting status */
        if
        :: (room.gasVolume >= room.upperBound) &&
           !room.venting ->
            room.venting = true;
            printf("Room %d is now VENTING (%d).\n", room.i, room.gasVolume);
            Vent_out ! M_VENT;
        :: (room.gasVolume <= room.lowerBound) &&
           room.venting ->
            room.venting = false;
            printf("Room %d is NO LONGER VENTING. (%d)\n", room.i, room.alarming);
            Vent_out ! M_UNVENT;
        :: else ->
            skip;
        fi;

        /* If venting; decrement gas volume */
        ventOnly:
        if
        :: room.venting ->
            room.gasVolume = room.gasVolume - room.ventRate;
            if
            :: room.gasVolume < 0 ->
                room.gasVolume = 0
            :: else ->
                skip
            fi;
        :: else ->
            skip;
        fi;
    od;
};

proctype FactoryController(chan Vent_in,
                                Alarm_out,
                                Reset_in) {
    int venting = 0;
    bool alarming = false;

    end: do
    /* If the alarm has been reset; stop alarming */
    :: Reset_in ? M_RESET ->
        printf("Factory NO LONGER in ALARM mode.\n");
        alarming = false;

        atomic {
            int i;
            for (i : 0 .. NUM_ROOMS - 1) {
                rooms[i].Alarm_in ! M_RESET;
            }
        }

    /* Increment num of rooms venting */
    :: Vent_in ? M_VENT ->
        venting++;

        if
        /* If the room is over the threshold; ALARM!!!!! */
        :: venting >= ALARM_THRESHOLD && !alarming ->
            alarming = true;
            atomic {
                int i;
                for (i : 0 .. NUM_ROOMS - 1) {
                    rooms[i].Alarm_in ! M_ALARM;
                }
                Alarm_out ! M_ALARM;
            }
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

    /* Reset alarms */
    end: do
    :: Alarm_in ? M_ALARM ->
        printf("Agent is RESETTING alarm.\n");
        Reset_out ! M_RESET;
    od;
};

/* Room fields */
chan Clock[NUM_ROOMS] = [0] of {mtype};
chan RoomAlarm[NUM_ROOMS] = [0] of {mtype};

/* Global variables */
chan Vent = [0] of {mtype};
chan FactoryAlarm = [0] of {mtype};
chan Reset = [0] of {mtype};

init {

    /* Initialise rooms */
    {
        int i;
        for (i : 0 .. NUM_ROOMS - 1) {
            rooms[i].lowerBound = 10;
            rooms[i].upperBound = 20;
            rooms[i].volume = 1000;
            rooms[i].ventRate = 5;
            rooms[i].gasRate = 1;
        }
    }

    atomic {
        int i;
        for (i : 0 .. NUM_ROOMS - 1) {
            rooms[i].i = i;
            rooms[i].Clock_in = Clock[i];
            rooms[i].Alarm_in = RoomAlarm[i];

            run RoomController(rooms[i], Vent);
        }
        run FactoryController(Vent, FactoryAlarm, Reset);
        run Agent(FactoryAlarm, Reset);
    }

    /* Increment clock */
    do
    :: atomic {
        int i;
        for (i : 0 .. NUM_ROOMS - 1) {
            rooms[i].Clock_in ! M_TICK;
        }
    }
    od;
}
