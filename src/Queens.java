package csp_solver;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import javafx.util.Pair;

public class Queens {
    private ConstraintSatisfactionProblem solver = new ConstraintSatisfactionProblem();
    private int numberOfQueens;
    
    @SuppressWarnings({ "restriction", "boxing" })
    public Queens(int queens) {
        numberOfQueens = queens;
        Set<Integer> domain = new HashSet<>();
        for (int i = 1; i <= numberOfQueens; ++i)
            domain.add(i);
        // Create variables
        for (int i = 1; i <= numberOfQueens; ++i)
            solver.addVariable(i, domain);
        // Create constraints
        for (int i = 1; i <= numberOfQueens - 1; ++i) {
            for (int j = i + 1; j <= numberOfQueens; ++j) {
                Set<Pair<Integer, Integer>> constraint = new HashSet<>();
                for (int a = 1; a <= numberOfQueens; ++a) {
                    for (int b = 1; b <= numberOfQueens; ++b) {
                        if (a == b || Math.abs(a - b) == Math.abs(i - j))
                            continue;
                        constraint.add(new Pair<>(a, b));
                    }
                }
                solver.addConstraint(i, j, constraint);
            }
        }
    }
    
    private static boolean verify(int[] solution) {
        if (solution == null)
            return false;
        for (int i = 0; i < solution.length - 1; ++i) {
            for (int j = i + 1; j < solution.length; ++j) {
                if (solution[i] == solution[j])
                    return false;
                if (Math.abs(i - j) == Math.abs(solution[i] - solution[j]))
                    return false;
            }
        }
        return true;
    }
    
    @SuppressWarnings("boxing")
    public int[] solve() {
        Map<Integer, Integer> solution = solver.solve();
        if (solution == null)
            return null;
        int[] result = new int[numberOfQueens];
        for (int i = 1; i <= numberOfQueens; ++i)
            result[i - 1] = solution.get(i);
        return result;
    }
    
    public static final void main(String[] args) {
        int[] solution = new Queens(8).solve();
        if (!Queens.verify(solution))
            System.out.println("Solution not found");
        else
            System.out.println(Arrays.toString(solution));
    }
}
