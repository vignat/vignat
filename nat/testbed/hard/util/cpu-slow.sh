#!/bin/bash
# Run CPU on a ~third of the maximum frequency (scale-down)
# Not used (yet?)

for i in $(seq 1 31); do echo userspace > /sys/devices/system/cpu/cpu$i/cpufreq/scaling_governor; done
for i in $(seq 1 31); do echo 1200000 > /sys/devices/system/cpu/cpu$i/cpufreq/scaling_setspeed; done
