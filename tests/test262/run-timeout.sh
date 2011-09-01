#!/bin/bash
timeout=4
interval=2
(
    ((t = timeout))

    while ((t > 0)); do
        sleep $interval
        kill -0 $$ || exit 0
        ((t -= interval))
    done

    # Clean up after ourselves so we don't leave temps around and
    # we're killing the process that's supposed to clean up
    rm -rf /tmp/js.*
    rm -rf /tmp/json.*
    rm -rf /tmp/stripped.*
    rm -rf /tmp/result.*

    # Be nice, post SIGTERM first.
    # The 'exit 0' below will be executed if any preceeding command fails.
    kill -s SIGTERM $$ && kill -0 $$ || exit 0
    sleep $delay
    kill -s SIGKILL $$
) 2> /dev/null &

exec ./single-test.sh $1
