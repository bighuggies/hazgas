#define NUM_ROOMS 1

mtype = {
    M_TICK,
    M_VENT,
    M_UNVENT,
    M_ALARM,
    M_RESET
};

int alarmThreshold = 10;
bool alarming = false;

typedef Room {
    int i;

    int lowerBound;
    int upperBound;
    int volume;
    int gasVolume;

    int ventRate;
    int gasRate;

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
        :: room.gasVolume >= room.upperBound * room.volume / 100 ->
            room.venting = true;
            Vent_out ! M_VENT;
        :: room.gasVolume <= room.lowerBound * room.volume / 100 ->
            room.venting = false;
            Vent_out ! M_UNVENT;
        fi;

        if
        :: room.venting ->
            room.gasVolume = room.gasVolume - room.ventRate;
        fi;
    od;
};

proctype FactoryController(chan Clock_in,
                                Vent_in,
                                Alarm_out,
                                Reset_in) {
    int venting = 0;
    do
    :: Vent_in ? M_VENT ->
        venting++;
        if
        :: venting >= alarmThreshold * NUM_ROOMS / 100 ->
            Alarm_out ! M_ALARM
        fi
    :: Vent_in ? M_UNVENT ->
        venting--;
    :: Reset_in ? M_RESET ->
        alarming = false;
    od;
};

proctype Agent(chan Alarm_in,
                    Reset_out) {
    do
    :: Alarm_in ? M_ALARM ->
        skip
    od;
};

init {
    chan Clock = [0] of {mtype};
    chan Vent = [NUM_ROOMS] of {mtype};
    chan Reset = [0] of {mtype};
    chan Alarm = [0] of {mtype};

    atomic {
        int i = 0;
        do
        :: (i == NUM_ROOMS) ->
            break;
        :: (i < NUM_ROOMS) ->
            rooms[i].i = i;
            run RoomController(rooms[i], Clock, Vent, Alarm);
            i++;
        od;
        run FactoryController(Clock, Vent, Reset, Alarm);
    }

    do
    :: Clock ! M_TICK ->
        skip;
    od;
}
