#!/bin/bash

# Load the configuration
. ./config.sh

# Clone the scripts
rsync -tv -r ./ $TESTER_HOST:scripts
rsync -tv -r ./ $SERVER_HOST:scripts

# Initialize all machines
ssh $TESTER_HOST 'bash ~/scripts/init/tester.sh'
ssh $SERVER_HOST 'bash ~/scripts/init/server.sh'
. ./init/middlebox.sh
