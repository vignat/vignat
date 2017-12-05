#!/bin/bash

vagrant ssh -c 'sudo python /vagrant/scenarios/send-receive/server.py 2>&1 >/dev/null' server 2>&1 >/dev/null &
sleep 0.1
vagrant ssh -c 'sudo python /vagrant/scenarios/send-receive/client.py 2>&1 >/dev/null' client 2>&1 >/dev/null

if [ $? -eq 0 ]; then
    echo "send-receive OK"
else
    echo "send-receive FAIL"
fi

vagrant ssh -c 'sudo python /vagrant/scenarios/send-expire/server.py 2>&1 >/dev/null' server 2>&1 >/dev/null &
sleep 0.1
vagrant ssh -c 'sudo python /vagrant/scenarios/send-expire/client.py 2>&1 >/dev/null' client 2>&1 >/dev/null

if [ $? -eq 0 ]; then
    echo "send-expire OK"
else
    echo "send-expire FAIL"
fi

vagrant ssh -c 'sudo python /vagrant/scenarios/listen-forbid/server.py 2>&1 >/dev/null' server 2>&1 >/dev/null &
vagrant ssh -c 'sudo python /vagrant/scenarios/listen-forbid/client.py 2>&1 >/dev/null' client 2>&1 >/dev/null

if [ $? -eq 0 ]; then
    echo "listen-forbid OK"
else
    echo "listen-forbid FAIL"
fi

vagrant ssh -c 'sudo python /vagrant/scenarios/send-hijack/server.py 2>&1 >/dev/null' server 2>&1 >/dev/null &
sleep 0.1
vagrant ssh -c 'sudo python /vagrant/scenarios/send-hijack/client.py 2>&1 >/dev/null' client 2>&1 >/dev/null

if [ $? -eq 0 ]; then
    echo "send-hijack OK"
else
    echo "send-hijack FAIL"
fi
