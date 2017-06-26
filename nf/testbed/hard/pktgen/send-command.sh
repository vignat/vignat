#!/bin/bash
# Send a command to a pktgen server running on the port 22022
# The first argument ($1) is the command to be sent.

socat - TCP4:localhost:22022 < $1
