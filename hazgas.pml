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
                        chan Clock_in,
                             Alarm_in,
                             Vent_out) {
    do
    :: Alarm_in ? M_ALARM ->
        room.venting = true;
        Vent_out ! M_VENT;

    :: Clock_in ? M_TICK ->
        room.gasVolume = room.gasVolume + room.gasRate;

        if
        :: alarming ->
            goto after;
        :: else ->
            skip;
        fi;

        if
        :: room.gasVolume >= (room.upperBound * room.volume / 100) &&
           !room.venting ->
            room.venting = true;
            printf("Room %d is now VENTING.\n", room.i);
            Vent_out ! M_VENT;
        :: room.gasVolume <= (room.lowerBound * room.volume / 100) &&
           room.venting ->
            room.venting = false;
            printf("Room %d is NO LONGER VENTING.\n", room.i);
            Vent_out ! M_UNVENT;
        :: else ->
            skip;
        fi;

        after:
        if
        :: room.venting ->
            room.gasVolume = room.gasVolume - room.ventRate;
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
    :: Vent_in ? M_VENT ->
        venting++;
        if
        :: venting >= ALARM_THRESHOLD * NUM_ROOMS / 100 ->
            printf("Factory in ALARM mode.\n");
            Alarm_out ! M_ALARM;
            alarming = true;
        :: else ->
            skip;
        fi;
    :: Vent_in ? M_UNVENT ->
        venting--;
    :: Reset_in ? M_RESET ->
        printf("Factory NO LONGER in ALARM mode.\n");
        alarming = false;
    od;
};

proctype Agent(chan Alarm_in,
                    Reset_out) {
    do
    :: Alarm_in ? M_ALARM ->
        Reset_out ! M_RESET
    od;
};

init {
    chan Clock[NUM_ROOMS] = [0] of {mtype};

    chan Vent = [NUM_ROOMS] of {mtype};
    chan Reset = [0] of {mtype};
    chan Alarm = [0] of {mtype};

    rooms[0].lowerBound = 2;
    rooms[0].upperBound = 5;
    rooms[0].volume = 1000;
    rooms[0].ventRate = 15;
    rooms[0].gasRate = 10;

    atomic {
        int i = 0;
        do
        :: (i == NUM_ROOMS) ->
            break;
        :: else ->
            rooms[i].i = i;
            run RoomController(rooms[i], Clock[i], Vent, Alarm);
            i++;
        od;
        run FactoryController(Vent, Reset, Alarm);
        run Agent(Alarm, Reset);
    }

    do
    :: atomic {
        int i = 0;
        do
        :: (i == NUM_ROOMS) ->
            break;
        :: else ->
            rooms[i].i = i;
            Clock[i] ! M_TICK;
            i++;
        od;
    }
    od;
}
