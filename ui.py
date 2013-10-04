#!/usr/bin/env python
import subprocess
import sys
import threading

class AgentThread(threading.Thread):
    daemon = True

    def __init__(self, process, *args, **kwargs):
        super(AgentThread, self).__init__(*args, **kwargs)
        self.process = process

    def run(self):
        while True:
            self.process.stdin.write(raw_input())
            self.process.stdin.flush()

p = subprocess.Popen(["spin", "-T", "hazgas.pml"], stdin=subprocess.PIPE,
                                                   stdout=subprocess.PIPE)

AgentThread(p).start()
while True:
    sys.stdout.write(p.stdout.read(1))
