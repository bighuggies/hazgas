#!/usr/bin/env python

import atexit
import signal
import subprocess
import sys
import threading
import time

from Tkinter import *


p = subprocess.Popen(["spin", "-DUI", "-T", "hazgas.pml"], stdin=subprocess.PIPE,
                                                           stdout=subprocess.PIPE)

@atexit.register
def kill_child():
    p.send_signal(signal.SIGTERM)


class Room(object):
    def __init__(self, i, volume, lower_bound, upper_bound, vent_rate, gas_rate):
        self.i = i
        self.volume = volume
        self.lower_bound = lower_bound
        self.upper_bound = upper_bound
        self.vent_rate = vent_rate
        self.gas_rate = gas_rate

        self.gas_volume = 0
        self.venting = False

    def __repr__(self):
        return "<Room: {volume}L, gas > {lower_bound}L, gas < {upper_bound}L, gas -{vent_rate}L/s+{gas_rate}L/s, gas @ {gas_volume}L>".format(**self.__dict__)

# read the number of rooms
num_rooms = int(p.stdout.readline().strip())
rooms = [None] * num_rooms
tick = 0

# plot rooms on canvas
MARGIN = 5
SCALE = 5

width = 0
height = 50

x_offsets = []

for _ in range(num_rooms):
    i, volume, lower_bound, upper_bound, vent_rate, gas_rate = map(int, p.stdout.readline().strip().split(":"))
    rooms[i] = Room(i, volume, lower_bound, upper_bound, vent_rate, gas_rate)

    x_offsets.append(width)
    width += volume // height

print(rooms)

root = Tk()
root.wm_title("Hazgas")
c = Canvas(root, width=(width + MARGIN * (1 + num_rooms)) * SCALE,
                 height=(height + MARGIN * 2) * SCALE)
c.pack()

for room in rooms:
    left = MARGIN * (room.i + 1) + x_offsets[room.i]
    w = room.volume // height

    c.create_rectangle(left * SCALE, MARGIN * SCALE,
                       (left + w) * SCALE, (MARGIN + height) * SCALE,
                       fill="white", tag=("room", "room-{0}".format(room.i)))

    c.create_rectangle(left * SCALE, (MARGIN + height) * SCALE,
                       (left + w) * SCALE, (MARGIN + height) * SCALE,
                       fill="green", tags=("gas", "gas-{0}".format(room.i)))

    c.create_rectangle(left * SCALE, (MARGIN + height - room.lower_bound // w) * SCALE,
                       (left + w) * SCALE, (MARGIN + height - room.upper_bound // w) * SCALE,
                       outline="red", tags=("bounds", "bounds-{0}".format(room.i)))

alarming = False
reset_alarm_next_tick = False

def do_reset():
    global reset_alarm_next_tick
    reset_alarm_next_tick = True

tick_label = Label(root, text=str(tick))
tick_label.pack()

def process():
    global alarming, reset_alarm_next_tick, tick

    l = p.stdout.readline().strip()

    if l == "!":
        alarming = True

        if reset_alarm_next_tick:
            p.stdin.write(".")
            reset_alarm_next_tick = False
        else:
            p.stdin.write(",")
        p.stdin.flush()
    elif l == ".":
        alarming = False
    elif l == "t":
        tick += 1
        tick_label.config(text=str(tick))
    else:
        i, gas_volume, venting = map(int, l.split(":"))

        rooms[i].gas_volume = gas_volume
        rooms[i].venting = bool(venting)

    redraw()

    root.after(1, process)


def redraw():
    c.config(background="red" if alarming else "white")

    for room in rooms:
        left = MARGIN * (room.i + 1) + x_offsets[room.i]
        w = room.volume // height

        gas_height = room.gas_volume // w

        c.coords("gas-{0}".format(room.i),
                 left * SCALE, (MARGIN + height - gas_height) * SCALE,
                 (left + w) * SCALE, (MARGIN + height) * SCALE)

        c.itemconfig("room-{0}".format(room.i),
                     fill="blue" if room.venting else "white")

process()
mainloop()
