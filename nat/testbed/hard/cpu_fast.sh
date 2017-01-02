#!/bin/bash
# Run the CPU on full frequency (hopefully)
# Not used (yet?)

for i in $(seq 1 31); do echo userspace > /sys/devices/system/cpu/cpu$i/cpufreq/scaling_governor; done
for i in $(seq 1 31); do echo 3300000 > /sys/devices/system/cpu/cpu$i/cpufreq/scaling_setspeed; done
