SRCS = ConstraintSatisfactionProblem.java hashPair.java

queens:
	javac -d . $(SRCS) Queens.java

sudoku:
	javac -d . $(SRCS) Sudoku.java

circ:
	javac -d . $(SRCS) Circuit.java

clean:
	rm ./csp_solver/*.class

runQ:
	javac -d . $(SRCS) Queens.java
	java csp_solver.Queens

runS:
	javac -d . $(SRCS) Sudoku.java
	java csp_solver.Sudoku

runC:
	javac -d . $(SRCS) Circuit.java
	java csp_solver.Circuit
