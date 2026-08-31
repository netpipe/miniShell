CC      ?= cc
CFLAGS  ?= -std=c99 -O2 -Wall -Wextra
LDFLAGS ?=

BIN  = minishell
SRC  = main.c

all: $(BIN)

$(BIN): $(SRC)
	$(CC) $(CFLAGS) -o $@ $(SRC) $(LDFLAGS)

# the recorded expectations came from dash/bash, so this can actually fail
check: $(BIN)
	python3 tests/run.py ./$(BIN)

# compare against the reference shells live instead of the recorded output
difftest: $(BIN)
	python3 tests/run.py ./$(BIN) --ref

# regenerate tests/expected.txt from the reference shells
regen:
	python3 tests/run.py ./$(BIN) --regen

# malformed and adversarial input: nothing may crash, hang or trip a sanitiser
fuzz:
	$(CC) -std=c99 -g -fsanitize=address,undefined -o $(BIN).san $(SRC)
	python3 tests/fuzz.py ./$(BIN).san

# the whole suite under AddressSanitizer, UndefinedBehaviorSanitizer and
# leak detection
asan:
	$(CC) -std=c99 -g -fsanitize=address,undefined -o $(BIN).san $(SRC)
	ASAN_OPTIONS=detect_leaks=1 python3 tests/run.py ./$(BIN).san

sample: $(BIN)
	./$(BIN) test.sh

clean:
	rm -f $(BIN) $(BIN).san

.PHONY: all check difftest regen fuzz asan sample clean
