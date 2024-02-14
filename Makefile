.PHONY: clean clean-all default

RUBBISH := ./certificate ./data/ ./*.sdpa ./report.html

default:
	@echo "empty"

clean:
	rm -rf ${RUBBISH}

clean-all:
	rm -rf ${RUBBISH} ./target
