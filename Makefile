.PHONY: all clean

all:
	c++ -std=c++17 lambda.cpp -o lambda
	c++ -std=c++11 template.cpp -o template
	c++ -std=c++26 coc.cpp -o coc

clean:
	rm -f lambda template coc
