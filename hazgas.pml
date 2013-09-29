#define NUM_ROOMS 1
#define ALARM_THRESHOLD 10

mtype = {
    M_TICK,
    M_VENT,
    M_UNVENT,
    M_ALARM,
    M_RESET
};

bool alarming = false;

typedef Room {
    int i;
    chan Clock_in;
    chan Alarm_in;

    int lowerBound;
    int upperBound;
    int volume;
    int ventRate;
    int gasRate;

    int gasVolume;

    bool venting;
};

Room rooms[NUM_ROOMS];

proctype RoomController(Room room;
                        chan Vent_out) {
    do
    :: room.Alarm_in ? M_ALARM ->
        printf("Room %d has received an ALARM.\n", room.i);

        if
        :: !room.venting ->
            Vent_out ! M_VENT;
            room.venting = true;
        :: else ->
            skip;
        fi;

    :: room.Clock_in ? M_TICK ->
        room.gasVolume = room.gasVolume + room.gasRate;

        if
        :: (room.gasVolume >= (room.upperBound * room.volume / 100)) &&
           !room.venting ->
            room.venting = true;
            printf("Room %d is now VENTING.\n", room.i);
            Vent_out ! M_VENT;
        :: (room.gasVolume <= (room.lowerBound * room.volume / 100)) &&
           room.venting && !alarming ->
            room.venting = false;
            printf("Room %d is NO LONGER VENTING. (%d)\n", room.i, alarming);
            Vent_out ! M_UNVENT;
        :: else ->
            skip;
        fi;

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

    do
    :: Reset_in ? M_RESET ->
        printf("Factory NO LONGER in ALARM mode.\n");
        alarming = false;
    :: Vent_in ? M_VENT ->
        venting++;
        if
        :: (venting >= ALARM_THRESHOLD * NUM_ROOMS / 100) &&
           !alarming ->
            printf("Factory in ALARM mode.\n");
            alarming = true;

            do
            :: atomic {
                Alarm_out ! M_ALARM;
                int i = 0;
                do
                :: (i == NUM_ROOMS) ->
                    break;
                :: else ->
                    rooms[i].Alarm_in ! M_ALARM;
                    i++;
                od;
            }
            od;
        :: else ->
            skip;
        fi;
    :: Vent_in ? M_UNVENT ->
        venting--;
    od;
};

proctype Agent(chan Alarm_in,
                    Reset_out) {
    do
    :: Alarm_in ? M_ALARM ->
        printf("Agent is RESETTING alarm.\n");
        Reset_out ! M_RESET;
    od;
};

chan Clock[NUM_ROOMS] = [0] of {mtype};
chan RoomAlarm[NUM_ROOMS] = [0] of {mtype};

chan Vent = [0] of {mtype};
chan FactoryAlarm = [0] of {mtype};
chan Reset = [0] of {mtype};

init {
    rooms[0].lowerBound = 2;
    rooms[0].upperBound = 5;
    rooms[0].volume = 1000;
    rooms[0].ventRate = 15;
    rooms[0].gasRate = 1;

    atomic {
        int i = 0;
        do
        :: (i == NUM_ROOMS) ->
            break;
        :: else ->
            rooms[i].i = i;
            rooms[i].Clock_in = Clock[i];
            rooms[i].Alarm_in = RoomAlarm[i];

            run RoomController(rooms[i], Vent);
            i++;
        od;
        run FactoryController(Vent, FactoryAlarm, Reset);
        run Agent(FactoryAlarm, Reset);
    }

    do
    :: atomic {
        int i = 0;
        do
        :: (i == NUM_ROOMS) ->
            break;
        :: else ->
            rooms[i].Clock_in ! M_TICK;
            i++;
        od;
    }
    od;
}
