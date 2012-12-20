#!/bin/bash
# Continuous build script
# XXX handle interrupts gracefully
NAME=logitext
if [ -f config ]
then
    . config
fi
while true
do
    reset
    pkill -f $NAME.exe
    (
        ghc -Wall -Werror --make -c ClassicalFOLFFI.hs && \
        #ghc -Wall -Werror --make -c LinearFFI.hs && \
        ghc -Wall -Werror --make -c IntuitionisticFFI.hs && \
        ghc -Wall -Werror --make -c haskell.c && \
        urweb $URWEB_FLAGS $NAME && \
        ./$NAME.exe
        #(./$NAME.exe &) && \
        #sleep 1 && \
        #(curl "http://localhost:8080/main" &> /dev/null)
    ) &
    PID=$!
    inotifywait -e modify $(git ls-files '*.ur' '*.urp' '*.urs' '*.hs' '*.c' '*.h') 2> /dev/null
    kill $PID
done
