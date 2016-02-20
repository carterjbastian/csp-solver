SRCS = ConstraintSatisfactionProblem.java hashPair.java

queens:
	javac -d . $(SRCS) Queens.java


clean:
	rm ./csp_solver/*.class

run:
	javac -d . $(SRCS) Queens.java
	java csp_solver.Queens
