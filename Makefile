.PHONY: clean default

default:
	@echo "empty"

clean:
	rm -rf ./certificate ./data/ ./target/ ./*.sdpa ./report.html
