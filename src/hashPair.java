package csp_solver;

import javafx.util.Pair;
    /**
     * A Pair class that will hash correctly
     *
     */
    public class hashPair {
      private Pair<Integer, Integer> p;

      public hashPair(Integer x, Integer y) {
        p = new Pair<Integer, Integer>(x, y);
      }

      public Integer getX() {
        return p.getKey();
      }

      public Integer getY() {
        return p.getValue();
      }

      public int hashCode() {
        int x = getX();
        int y = getY();
        return (x * 100) + y;
      }

      public boolean equals(Object o) {
        if (! (o instanceof hashPair) )
          return false;

        return (getX() == ((hashPair)o).getX() && getY() == ((hashPair)o).getY());
      }
    }
