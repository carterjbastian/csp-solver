package csp_solver;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import javafx.util.Pair;

public class Circuit {
    private ConstraintSatisfactionProblem solver = new ConstraintSatisfactionProblem();
    private int rows;
    private int cols;
    private CircuitPiece[] pieces;
    
    public static class CircuitPiece {
      public int w;
      public int h;
      public char c;
      
      public CircuitPiece(int width, int height, char representation) {
        w = width;
        h = height;
        c = representation;
      }

      @Override
      public String toString() {
        return (c + ": (" + w + " x " + h + ")");
      } 
    }

    public Circuit(int r, int c, CircuitPiece[] ps) {
      rows = r;
      cols = c;
      pieces = ps;
  
      // Generate domains of all of the pieces
      for (int p = 0; p < pieces.length; p++) {
        Set<Integer> domain = new HashSet<Integer>();

        for (int i = 0; i <= this.cols - pieces[p].w; i++)
          for (int j = 0; j <= this.rows - pieces[p].h; j++)
            domain.add((j * this.cols) + i);
       
        solver.addVariable(p, domain);
      }

      // Generate Constraints for all combinations of pieces
      for (int p1 = 0; p1 < pieces.length - 1; p1++) {
        for (int p2 = p1 + 1; p2 < pieces.length; p2++) {
          Set<hashPair> constraint = new HashSet<hashPair>();

          // Loop through the domain of piece 1
          for (Integer val1 : solver.Variables.get(p1)) {
            // And the domain of of piece 2
            for (Integer val2 : solver.Variables.get(p2)) {
              // To check the validity of each combination
              if (! isConflict(pieces[p1], val1, pieces[p2], val2))
                  constraint.add(new hashPair(val1, val2));
            }
          }
          // Add the resulting constraint to the solver
          solver.addConstraint(p1, p2, constraint);
        }
      }

      
    }

    private boolean isConflict(CircuitPiece p1, int val1, CircuitPiece p2, int val2) {
      Set<Integer> p1Claimed = new HashSet<Integer>();
      Set<Integer> p2Claimed = new HashSet<Integer>();

      // Build the set of all places on circuitboard claimed by piece 1
      int xStart = val1 % this.cols;
      int yStart = val1 / this.cols; // Note the integer division

      for (int y = yStart; y < (yStart + p1.h); y++)
        for (int x = xStart; x < (xStart + p1.w); x++)
          p1Claimed.add(y * this.cols + x);

      // Build the set of all places on circuitboard claimed by piece 2
      xStart = val2 % this.cols;
      yStart = val2 / this.cols; // Note the integer division

      for (int y = yStart; y < (yStart + p2.h); y++)
        for (int x = xStart; x < (xStart + p2.w); x++)
          p2Claimed.add(y * this.cols + x);

      // If the intersection of these two sets is nonempty, there is a conflict
      p1Claimed.retainAll(p2Claimed);
      return (! p1Claimed.isEmpty());
    }

    private char[] solve() {
      Map<Integer, Integer> solution = solver.solve();
      if (solution == null)
        return null;

      int maxVal = rows * cols;
      char[] result = new char[maxVal];

      // Fix with initial periods
      for (int i = 0; i < maxVal; i++)
        result[i] = '.';

      for (Integer var : solution.keySet()) {
        int val = solution.get(var);
        CircuitPiece p = pieces[var];
        int xStart = val % this.cols;
        int yStart = val / this.cols;

        for (int y = yStart; y < (yStart + p.h); y++)
          for (int x = xStart; x < (xStart + p.w); x++)
            result[y * this.cols + x] = p.c;
      }

      return result;
    }

    public static final void main(String[] args) {
      // Make the pieces from the example
      CircuitPiece[] pArr = new CircuitPiece[4];
      pArr[0] = new CircuitPiece(3, 2, 'a');
      pArr[1] = new CircuitPiece(5, 2, 'b');      
      pArr[2] = new CircuitPiece(2, 3, 'c');      
      pArr[3] = new CircuitPiece(7, 1, 'e');

      System.out.println(pArr);
      Circuit circ = new Circuit(3, 10, pArr);
      char[] solution = circ.solve();
      if (solution == null)
        System.out.println("Did not find a solution");

      int i = 0;
      for (int y = 0; y < circ.rows; y++) {
        for (int x = 0; x < circ.cols; x++) {
          System.out.print(solution[i]);
          i++;
        }
        System.out.print("\n");
      } 
    }
    
}
