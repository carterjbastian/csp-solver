package csp_solver;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Iterator;
import javafx.util.Pair;
import java.util.LinkedList;

/**
 * Simple CSP solver
 *
 */
public class ConstraintSatisfactionProblem {
    public final int MAX_CAPACITY = 1000000;
    private int nodesExplored;
    private int constraintsChecked;

    private boolean MRV;
    private boolean LCV;
    private boolean AC3;
    private boolean MAC3;

    private Map<Integer, Set<Integer>> Variables;
    
    // Let's be real: This is one nasty-looking data structure.
    //    Breakdown: We got a Pair of Variables
    //    This maps to a set of acceptable values of these two variables.
    private Map<hashPair, Set<hashPair>> Constraints;

    private ArrayList<Map<Integer, Set<Integer>>> removedLogs;
    private ArrayList<Map<Integer, Integer>> addLogs;

    public ConstraintSatisfactionProblem() {
      nodesExplored = 0;
      constraintsChecked = 0;

      /* USE THIS SECTION TO MODIFY ACTIVE FEATURES */
      this.MRV = true;
      this.LCV = true;
      this.AC3 = true;
      this.MAC3 = true;

      Variables = new HashMap<Integer, Set<Integer>>();
      Constraints = new HashMap<hashPair, Set<hashPair>>();

      removedLogs = new ArrayList<Map<Integer, Set<Integer>>>();
      addLogs = new ArrayList<Map<Integer, Integer>>();
      removedLogs.ensureCapacity(MAX_CAPACITY);
      addLogs.ensureCapacity(MAX_CAPACITY);
      removedLogs.add(new HashMap<Integer, Set<Integer>>());
      addLogs.add(new HashMap<Integer, Integer>());
    }

    /**
     * Solve for the CSP problem
     * @return the mapping from variables to values
     */
    public Map<Integer, Integer> solve() {
        resetStats();
        long before = System.currentTimeMillis();
        if (!enforceConsistency(new HashMap<Integer, Set<Integer>>()))
            return null;
        Map<Integer, Integer> solution = backtracking(new HashMap<>(), 0);
        double duration = (System.currentTimeMillis() - before) / 1000.0;
        printStats();
        System.out.println(String.format("Search time is %.2f second", duration));
        return solution;
    }
    
    private void resetStats() {
        nodesExplored = 0;
        constraintsChecked = 0;
    }
    
    private void incrementNodeCount() {
        ++nodesExplored;
    }
    
    private void incrementConstraintCheck() {
        ++constraintsChecked;
    }
    
    public int getNodeCount() {
        return nodesExplored;
    }
    
    public int getConstraintCheck() {
        return constraintsChecked;
    }
    
    protected void printStats() {
        System.out.println("Nodes explored during last search:  " + nodesExplored);
        System.out.println("Constraints checked during last search " + constraintsChecked);
    }

    /**
     * Add a variable with its domain
     * @param id      the identifier of the variable
     * @param domain  the domain of the variable
     */
    public void addVariable(Integer id, Set<Integer> domain) {
      Set<Integer> copy = new HashSet<Integer>(domain);
      this.Variables.put(id, copy);
    }
    
    /**
     * Add a binary constraint
     * @param id1         the identifier of the first variable
     * @param id2         the identifier of the second variable
     * @param constraint  the constraint
     */
    public void addConstraint(Integer id1, Integer id2, Set<hashPair> constraint) {
      hashPair scope = new hashPair(id1, id2);
      this.Constraints.put(scope, constraint);
    }
    
    /**
     * Enforce consistency by AC-3, PC-3.
     */
    private boolean enforceConsistency(Map<Integer, Set<Integer>> removed) {
      if (this.AC3) {
        /* AC-3 Implementation */
        Queue<hashPair> arcQ = new LinkedList<hashPair>();
        
        // Make the arc Queue
        for (hashPair arc : Constraints.keySet()) 
          arcQ.add(arc);
        
        // Arc Queue contains all of the initial arcs (constraint pairs)
        
        // Loop while the queue is not empty
        while (! arcQ.isEmpty()) {
          hashPair arc = arcQ.remove();

          if (revise(arc, removed)) {
            if (this.Variables.get(arc.getX()).size() == 0)
              return false;
            for (hashPair modded : Constraints.keySet()) {
              if ((modded.getX() == arc.getX() && modded.getY() != arc.getY()) ||
                  (modded.getY() == arc.getX()))
                arcQ.add(modded);
            }
          }

          if (reviseBackward(arc, removed)) {
            if (this.Variables.get(arc.getY()).size() == 0)
              return false;
            for (hashPair modded : Constraints.keySet()) {
              if ((modded.getY() == arc.getY() && modded.getX() != arc.getX()) ||
                  (modded.getX() == arc.getY()))
                arcQ.add(modded);
            }
          }

        }

        return true;
      } else {
        return true;
      }
    }
    
    private boolean revise(hashPair arc, Map<Integer, Set<Integer>> removed) {
        Integer id1 = arc.getX(), id2 = arc.getY();
        boolean revised = false;
        Iterator<Integer> domainIt = this.Variables.get(id1).iterator();

        // Loop through each value in the domain of X_i
        while (domainIt.hasNext()) {
//        for (Integer x : this.Variables.get(id1)) {
          Integer x = domainIt.next();
          boolean useless = true;
          for (Integer y : this.Variables.get(id2)) {
            hashPair attempt = new hashPair(x, y);
            if (Constraints.get(arc).contains(attempt))
                useless = false;
          }

          if (useless) {
//            System.out.println("Removing a Var in revise forward");
            if (removed.containsKey(id1)) {
              removed.get(id1).add(x);
            } else {
              removed.put(id1, new HashSet<Integer>());
              removed.get(id1).add(x);
            }
            domainIt.remove();
            revised = true;
          }
        }
        return revised;
    }

    private boolean reviseBackward(hashPair arc, Map<Integer, Set<Integer>>removed) {
        Integer id1 = arc.getX(), id2 = arc.getY();
        boolean revised = false;
        Iterator<Integer> domainIt = this.Variables.get(id2).iterator();

        // Loop through each value in the domain of X_j
        while (domainIt.hasNext()) {
          Integer y = domainIt.next();
          boolean useless = true;

          for (Integer x : this.Variables.get(id1)) {
            hashPair attempt = new hashPair(x, y);
            if (Constraints.get(arc).contains(attempt))
                useless = false;
          }

          if (useless) {
//            System.out.println("Removing a Var in revise backward");
            if (removed.containsKey(id2)) {
              removed.get(id2).add(y);
            } else {
              removed.put(id2, new HashSet<Integer>());
              removed.get(id2).add(y);
            }
            domainIt.remove();
            revised = true;
          }
        }
        return revised;
    }
    /**
     * Backtracking algorithm
     * @param partialSolution  a partial solution
     * @return a solution if found, null otherwise.
     */
    private Map<Integer, Integer> backtracking(Map<Integer, Integer> partialSolution, int depth) {
      if (depth >= MAX_CAPACITY) {
        System.err.println("Maximum recursion depth exceeded");
        return null;
      }

      /* Check if this level of depth has a rLog and aLog yet */
      Map<Integer, Set<Integer>> removed = removedLogs.get(depth);
      Map<Integer, Integer> added = addLogs.get(depth);

      /* Sanity Check: */
/*  
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("partialSolution At Start of Depth " + depth + ": " + partialSolution);
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("Domains At Start of Depth " + depth + ": " + this.Variables);
        System.out.println("\n");
*/
        Integer unassignedVar = selectUnassignedVariable(partialSolution);
      
      if (unassignedVar == -1)
        return partialSolution; // All variables have been adequately assigned

      List<Integer> domainVals = orderDomainValues(unassignedVar, partialSolution);

      Integer[] domainArray = new Integer[domainVals.size()];
      int i = 0;
      for (Integer x : domainVals) {
        domainArray[i] = x;
        i++;
      }
      
      int domainCount = domainArray.length;
      
      Map<Integer, Integer> result;

      // Loop through each potential value in the unassigned variable's domain
      for (i = 0; i < domainCount; i++) {
/*
        if (depth == 0)
          System.out.println("Domains: " + this.Variables);
*/ 
        Integer x = domainArray[i];

        /* SANITY CHECK */
/*
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("Trying (" + unassignedVar + " => " + x + ")");
*/
        // Make the assigment
        partialSolution.put(unassignedVar, x);
        added.put(unassignedVar, x); /* Add this entry to the aLog */
        incrementNodeCount();

        // Do the inference (and ensure this won't cause directly awful issues)
        if (inference(unassignedVar, x, partialSolution, removed, added)) { // Changes partialSolution by reference
          removedLogs.add(new HashMap<Integer, Set<Integer>>());
          addLogs.add(new HashMap<Integer, Integer>());
          result = backtracking(partialSolution, depth + 1); // Recurse on the updated solution

          // Check for success
          if (result != null) {
            /* We've succeeded! Don't undo anything */
            return result;
          }
        }

        /* SANITY CHECK */
/*
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("Restoring previous state!");
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("partialSolution Before: " + partialSolution);
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("Domains Before: " + this.Variables);
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("Removed Map: " + removed);
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("Added Map: " + added);
*/
        // Undo all of the changes we just did so we can try again at this depth
        /* Remove entries based on the aLog */
        Set<Integer> addedSet = new HashSet<Integer>(added.keySet());

        // Loop through each variable added to the partial solution
        for (Integer r : addedSet) {
          partialSolution.remove(r); // Remove it from the partial solution
          //added.remove(r); // Clear that entry in the aLog
        }

        /* Remove inference's changes based on the rLog */
        Set<Integer> removedSet = new HashSet<Integer>(removed.keySet());
        // Loop through all variable's whose domains were modified
        for (Integer r : removedSet) {
          Set<Integer> fromDomainX = removed.get(r);
          // Loop through each value removed from X's domain
          for (Integer gone : fromDomainX) {
            this.Variables.get(r).add(gone); // Add it back
          }
          removed.remove(r); // Get rid of the whole entry in the rLog
        }

        /* SANITY CHECK */
/*
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("partialSolution After: " + partialSolution);
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("Domains After: " + this.Variables);
        System.out.println("\n");
*/
        removed = new HashMap<Integer, Set<Integer>>();
        added = new HashMap<Integer, Integer>();
//        this.Variables.get(unassignedVar).remove(x);
        /* Keep the removal of the value we just tried from this var's domain? */
      }

      // All the changes from this depth level have been undone
      if (depth >= 1) {
        removedLogs.remove(removedLogs.size() - 1);
        addLogs.remove(removedLogs.size() - 1);
      } 

      /* SANITY CHECK */
/* 
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("partialSolution At End of Depth " + depth + ": " + partialSolution);
        for (int t = 0; t < depth; t++)
          System.out.print("\t");
        System.out.println("Domains At End of Depth " + depth + ": " + this.Variables);
        System.out.println("\n"); 
*/
      return null;
    }
    
    /**
     * Inference for backtracking
     * Implement FC and MAC3
     * @param var              the new assigned variable
     * @param value            the new assigned value
     * @param partialSolution  the partialSolution
     * @param removed          the values removed from other variables' domains
     * @return true if the partial solution may lead to a solution, false otherwise.
     */
    private boolean inference(Integer var, Integer value, 
                                Map<Integer, Integer> partialSolution, 
                                Map<Integer, Set<Integer>> removed, 
                                Map<Integer, Integer> added) {

      Iterator<hashPair> constraintIter = Constraints.keySet().iterator();
      Set<hashPair> relation; 
      Integer tempVar;
      Iterator<Integer> domainIter;
      Integer potentialVal;
      hashPair tempConstraint;
      Set<Integer> tempDomain;

      for (Integer x : this.Variables.get(var)) {
        if (x != value) {
          if (removed.containsKey(var)) {
             removed.get(var).add(x);
          } else {
            removed.put(var, new HashSet<Integer>());
            removed.get(var).add(x);
          }
        }
      }

      this.Variables.put(var, new HashSet<Integer>());
      this.Variables.get(var).add(value);

      // Loop through each constraint in the CSP
      for (hashPair scope : Constraints.keySet()) {
        incrementConstraintCheck();
        // Check if this constraint involves the newly assigned value
        if (scope.getX() == var) {
          // this var is the first item in the pair
          tempVar = scope.getY();
          
          if (! partialSolution.containsKey(tempVar)) {
            // Get the possible set of acceptable constrained pairs
            relation = Constraints.get(scope);

            // Loop through each item in the domain of the constraint-connected
            // variable to check for consistency.
            domainIter = this.Variables.get(tempVar).iterator();
          
            while (domainIter.hasNext()) {
              potentialVal = domainIter.next();
              tempConstraint = new hashPair(value, potentialVal);
            
              // If this constraint is not in the acceptable set of constraints,
              // remove this value from the domain
              if (!relation.contains(tempConstraint) ) {
                domainIter.remove();
                if (removed.containsKey(tempVar)) {
                  removed.get(tempVar).add(potentialVal);
                } else {
                  removed.put(tempVar, new HashSet<Integer>());
                  removed.get(tempVar).add(potentialVal);
                }
                /* Mark this as removed in the rLog */
              }

            }
          }
        } else if (scope.getY() == var) {
          // This var is the second item in the pair
          tempVar = scope.getX();

          if (! partialSolution.containsKey(tempVar)) {
            // Get the possible set of acceptable constrained pairs
            relation = Constraints.get(scope);

            // Loop through as above
            domainIter = this.Variables.get(tempVar).iterator();

            while (domainIter.hasNext()) {
              potentialVal = domainIter.next();
              tempConstraint = new hashPair(potentialVal, value);

              if (!relation.contains(tempConstraint)) {
                domainIter.remove();
                /* Mark this as removed in the rLog */
                if (removed.containsKey(tempVar)) {
                  removed.get(tempVar).add(potentialVal);
                } else {
                  removed.put(tempVar, new HashSet<Integer>());
                  removed.get(tempVar).add(potentialVal);
                }
              }
            }
          }
        } 
      }
      if (this.MAC3)  
        enforceConsistency(removed);

      /* Loop through each remaining unassigned variable */
      for (Integer V : Variables.keySet()) {
        if (! partialSolution.containsKey(V)) {
          tempDomain = Variables.get(V);

          // Check if there's a possible value left for it...
          if (tempDomain.size() == 0) {
            return false;
          }

          // Check if there's only a singled possible value left...
          if (tempDomain.size() == 1) {
            // If so, update the possible solution and recurse
            domainIter = tempDomain.iterator();
            Integer newVal = domainIter.next();
            
            partialSolution.put(V, newVal);
            added.put(V, newVal);
            incrementNodeCount();
            

            // If this fails in inference, the outer solution is bad too
            // run it at the same depth to keep track of changes
            if (! inference(V, newVal, partialSolution, removed, added)) {
              return false;
            }
          }
        }
      }
      return true;
    }
 
    /**
     * Look-ahead value ordering
     * Pick the least constraining value (min-conflicts)
     * @param var              the variable to be assigned
     * @param partialSolution  the partial solution
     * @return an order of values in var's domain
     */
    private List<Integer> orderDomainValues(Integer var, Map<Integer, Integer> partialSolution) {
      if (this.LCV) {
        Set<Integer> vals = Variables.get(var);
        List<Integer> result = new LinkedList<Integer>();
        Map<Integer, Integer> constraintAmount = new HashMap<Integer, Integer>();

        // Loop through each value in the variable's domain
        for (Integer v : vals) {
          int constraintCount = 0;
            
          // Loop through the remaining variables (that aren't var)
          for (Integer x : this.Variables.keySet()) {
              // Ensure this is an unassigned variable that's not var
              if (x != var && (! partialSolution.containsKey(x))) {
                if (this.Variables.get(x).contains(v))
                  constraintCount += this.Variables.get(x).size() - 1;
                else
                  constraintCount += this.Variables.get(x).size();
              }
          }
          constraintAmount.put(v, constraintCount);
        }

        // Sort the List appropriately
        Set<Integer> toList = new HashSet<Integer>(constraintAmount.keySet());
        for (int i = 0; i < toList.size(); i++) {
          int leastConstraint = Integer.MAX_VALUE;
          int leastInt = Integer.MAX_VALUE;
          // Loop through the constraintAmount keys
          for (Integer val : constraintAmount.keySet()) {
            if (constraintAmount.get(val) < leastConstraint) {
              leastConstraint = constraintAmount.get(val);
              leastInt = val;
            }
          }

          result.add(leastInt);
          constraintAmount.remove(leastInt);
        }

        return result;

      } else {
        Set<Integer> vals = Variables.get(var);
        // We want to loop through this and change the values in the Variables object
        Set<Integer> copy = new HashSet<Integer>(vals); 
        List<Integer> res = new LinkedList<Integer>();
        for (Integer x : copy) {
          res.add(x);
        }
        return res;
      }
    }

    /**
     * Dynamic variable ordering
     * Pick the variable with the minimum remaining values or the variable with the max degree.
     * Or pick the variable with the minimum ratio of remaining values to degree.
     * @param partialSolution  the partial solution
     * @return one unassigned variable
     */
    private Integer selectUnassignedVariable(Map<Integer, Integer> partialSolution) {
      /* MRV */
      if (this.MRV) {
        Map<Integer, Integer> constraintAmount = new HashMap<Integer, Integer>();

        // Iterate through each potential variable in the problem
        for (Integer x : Variables.keySet()) {
          // If it hasn't been assigned to yet, let's track it
          if (partialSolution.get(x) == null) {
            constraintAmount.put(x, Variables.get(x).size());
          }
        }

        // Loop through to find the value with the highest number of constraining
        // values

        int maxVal = -1;
        Integer maxInt = new Integer(-1);

        for (Integer x : constraintAmount.keySet()) {
          if (constraintAmount.get(x) > maxVal) {
            maxVal = constraintAmount.get(x);
            maxInt = x;
          }
        } 

        return maxInt;

      } else {
        // Iterate through all the variables in the problem
        for (Integer x : Variables.keySet()) {
          // If it hasn't been assigned to yet, that's our variable!
          if (partialSolution.get(x) == null)
            return x;
        }
        return -1;
      }
    }
    
    /**
     * Backjumping
     * Conflict-directed-backjumping
     * @param partialSolution
     */
    private void jumpBack(Map<Integer, Integer> partialSolution) {
    }
}
