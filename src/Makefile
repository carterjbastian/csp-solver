SRCS = ConstraintSatisfactionProblem.java hashPair.java

queens:
	javac -d . $(SRCS) Queens.java

sudoku:
	javac -d . $(SRCS) Sudoku.java

clean:
	rm ./csp_solver/*.class

runQ:
	javac -d . $(SRCS) Queens.java
	java csp_solver.Queens

runS:
	javac -d . $(SRCS) Sudoku.java
	java csp_solver.Sudoku
