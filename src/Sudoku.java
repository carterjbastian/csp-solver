package csp_solver;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javafx.util.Pair;

public class Sudoku {
    private ConstraintSatisfactionProblem solver = new ConstraintSatisfactionProblem();
    private int boardSize;
    private int sqrt;
    private static final String SHORT_TEST = "sudoku_short";
    private static final String LONG_TEST = "sudoku_test";
    
    // Constructor
    @SuppressWarnings("boxing")
    public Sudoku(int[][] board) {
        boardSize = board.length;
        sqrt = (int) Math.sqrt(boardSize);
        assert(sqrt * sqrt == boardSize);
        Set<Integer> domain = new HashSet<>();
        for (int i = 1; i <= boardSize; ++i)
            domain.add(i);
        for (int i = 0; i < board.length; ++i) {
            for (int j = 0; j < board[i].length; ++j) {
                if (board[i][j] == 0)
                    solver.addVariable(i * boardSize + (j + 1), domain);
                else
                    solver.addVariable(i * boardSize + (j + 1), Collections.singleton(board[i][j]));
            }
        }
        // Enforce row
        for (int i = 0; i < boardSize; ++i) {
            int[] pieces = new int[boardSize];
            for (int j = 0; j < boardSize; ++j)
                pieces[j] = i * boardSize + (j + 1);
            generateConstraint(pieces);
        }
        // Enforce column
        for (int j = 0; j < boardSize; ++j) {
            int[] pieces = new int[boardSize];
            for (int i = 0; i < boardSize; ++i)
                pieces[i] = i * boardSize + (j + 1);
            generateConstraint(pieces);
        }
        // Enforce block
        for (int i = 0; i < boardSize; ++i) {
            int[] pieces = new int[boardSize];
            for (int j = 0; j < boardSize; ++j) {
                int row = (i / sqrt) * sqrt + j / sqrt;
                int column = (i * sqrt) % boardSize + j % sqrt;
                pieces[j] = row * boardSize + column + 1;
            }   
            generateConstraint(pieces);
        }
    }
    
    @SuppressWarnings({ "restriction", "boxing" })
    public void generateConstraint(int[] pieces) {
        Set<hashPair> constraint = new HashSet<>();
        for (int i = 1; i <= boardSize; ++i) {
            for (int j = 1; j <= boardSize; ++j) {
                if (i == j)
                    continue;
                constraint.add(new hashPair(i, j));
            }
        }
        for (int i = 0; i < pieces.length; ++i) {
            for (int j = 0; j < pieces.length; ++j) {
                if (i == j)
                    continue;
                solver.addConstraint(pieces[i], pieces[j], constraint);
            }
        }
    }
    
    @SuppressWarnings("boxing")
    public int[][] solve() {
        Map<Integer, Integer> solution = solver.solve();
        if (solution == null)
            return null;
        int[][] result = new int[boardSize][boardSize];
        for (int i = 0; i < boardSize; ++i)
            for (int j = 0; j < boardSize; ++j)
                result[i][j] = solution.get(i * boardSize + j + 1);
        return result;
    }
    
    @SuppressWarnings("boxing")
    public boolean verify(int[][] solution) {
        if (solution == null)
            return false;
        for (int i = 0; i < 9; ++i) {
            Set<Integer> test = new HashSet<>();
            for (int j = 0; j < 9; ++j)
                if (1 <= solution[i][j] && solution[i][j] <= 9)
                    test.add(solution[i][j]);
            if (test.size() != 9)
                return false;
            test.clear();
            for (int j = 0; j < 9; ++j)
                if (1 <= solution[j][i] && solution[j][i] <= 9)
                    test.add(solution[j][i]);
            if (test.size() != 9)
                return false;
            test.clear();
            for (int j = 0; j < boardSize; ++j) {
                int row = (i / sqrt) * sqrt + j / sqrt;
                int column = (i * sqrt) % boardSize + j % sqrt;
                if (1 <= solution[row][column] && solution[row][column] <= 9)
                    test.add(solution[row][column]);
            }
            if (test.size() != 9)
                return false;
        }
        return true;
    }
    
    public static int[][] transform(String[] board) {
        int[][] result = new int[board.length][board.length];
        for (int i = 0; i < board.length; ++i) {
            for (int j = 0; j < board[i].length(); ++j)
                result[i][j] = Character.getNumericValue(board[i].charAt(j));
        }
        return result;
    }
    
    public int getNodeCount() {
        return solver.getNodeCount();
    }
    
    public int getConstraintCheck() {
        return solver.getConstraintCheck();
    }
    
    @SuppressWarnings("boxing")
    public static final void benchmark() {
        Charset charset = Charset.forName("US-ASCII");
        Path file = FileSystems.getDefault().getPath(".", LONG_TEST);
        List<Integer> nodes = new ArrayList<>();
        List<Integer> constraints = new ArrayList<>();
        List<Double> durations = new ArrayList<>();
        double max = Double.NEGATIVE_INFINITY;
        String hardest = "";
        try (BufferedReader br = Files.newBufferedReader(file, charset)) {
            for (String b = br.readLine(); b != null; b = br.readLine()){
                String[] board = new String[9];
                for (int i = 0; i < 9; ++i) {
                    board[i] = b.substring(i * 9, (i + 1) * 9);
                }
                int[][] testBoard = transform(board);
                Sudoku sudoku = new Sudoku(testBoard);
                long before = System.currentTimeMillis();
                int[][] solution = sudoku.solve();
                if (!sudoku.verify(solution)) {
                    System.out.println("Solution not found for " + b);
                    break;
                }
                double duration = (System.currentTimeMillis() - before) / 1000.0;
                int exploredNode = sudoku.getNodeCount();
                int constraintCheck = sudoku.getConstraintCheck();
                nodes.add(exploredNode);
                constraints.add(constraintCheck);
                durations.add(duration);
                if (duration > max) {
                    max = duration;
                    hardest = b;
                }
            }
            double averageNodes = nodes.stream().mapToInt(Integer::intValue).average().getAsDouble();
            double averageConstraints = constraints.stream().mapToInt(Integer::intValue).average().getAsDouble();
            double averageDuration = durations.stream().mapToDouble(Double::doubleValue).average().getAsDouble();
            
            double varianceNodes = nodes.stream().mapToDouble(i -> (i - averageNodes) * (i - averageNodes))
                                                 .sum() / nodes.size();
            double varianceConstraints = constraints.stream().mapToDouble(i -> (i - averageConstraints) * (i - averageConstraints))
                                                             .sum() / constraints.size();
            double varianceDuration = durations.stream().mapToDouble(i -> (i - averageDuration) * (i - averageDuration))
                                                        .sum() / durations.size();

            
            int maxNodes = nodes.stream().mapToInt(Integer::intValue).max().getAsInt();
            int maxConstraints = constraints.stream().mapToInt(Integer::intValue).max().getAsInt();
            double maxDuration = durations.stream().mapToDouble(Double::doubleValue).max().getAsDouble();
            System.out.println(averageNodes);
            System.out.println(String.format("Running time: avg %.2f max %.2f variance %.2f", averageDuration, maxDuration, varianceDuration));
            System.out.println(String.format("Explored nodes: avg %.2f max %d variance %.2f", averageNodes, maxNodes, varianceNodes));
            System.out.println(String.format("Constraints checked: avg %.2f max %d variance %.2f", averageConstraints, maxConstraints, varianceConstraints));
            System.out.println("Hardest instance: " + hardest);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
    
    private static int[][] easyBoard;
    private static int[][] mediumBoard;
    private static int[][] hardBoard;
    static {
        String[] easy = {"518700030", 
                         "003509068", 
                         "090084501",
                         "080630190",
                         "035041600",
                         "107005840",
                         "600428009",
                         "824000706",
                         "300170082"};
        easyBoard =transform(easy);
        String[] medium = {"000053080",
                           "300800000",
                           "000074150",
                           "200300060",
                           "103000508",
                           "050001004",
                           "097640000",
                           "000007002",
                           "020930000"};
        mediumBoard = transform(medium);
        String[] hard = {"000000201",
                         "004030000",
                         "000000000",
                         "370000080",
                         "600200000",
                         "000500000",
                         "540000600",
                         "000070040",
                         "002001000"};
        hardBoard = transform(hard);
    }
    
    public static final void main(String[] args) {
        //benchmark();
        Sudoku sudoku = new Sudoku(easyBoard);
        int[][] solution = sudoku.solve();
        if (!sudoku.verify(solution))
            System.out.println("Solution not found");
        else {
            for (int i = 0; i < 9; ++i)
                System.out.println(Arrays.toString(solution[i]));
        }
    }
}
