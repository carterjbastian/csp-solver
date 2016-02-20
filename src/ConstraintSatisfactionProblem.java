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


/**
 * Simple CSP solver
 *
 */
public class ConstraintSatisfactionProblem {
    public final int MAX_CAPACITY = 1000000;
    private int nodesExplored;
    private int constraintsChecked;

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

      Variables = new HashMap<Integer, Set<Integer>>();
      // #gross
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
        if (!enforceConsistency())
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
    private boolean enforceConsistency() {
        return true;
    }
    
    private boolean revise(Integer id1, Integer id2) {
        return false;
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

      Set<Integer> domainVals = orderDomainValues(unassignedVar, partialSolution);

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


      
      // Loop through and remove the new assignment from each domain
      for (Integer x : Variables.keySet()) {
        if (Variables.get(x).contains(value) ) {
          /* mark this as removed in the rLogs */
          Variables.get(x).remove(value);
          if (removed.containsKey(x)) {
            removed.get(x).add(value);
          } else {
            removed.put(x, new HashSet<Integer>());
            removed.get(x).add(value);
          }
        }
      }

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
    private Set<Integer> orderDomainValues(Integer var, Map<Integer, Integer> partialSolution) {
      Set<Integer> vals = Variables.get(var);
      // We want to loop through this and change the values in the Variables object
      Set<Integer> copy = new HashSet<Integer>(vals); 
      return vals;
    }

    /**
     * Dynamic variable ordering
     * Pick the variable with the minimum remaining values or the variable with the max degree.
     * Or pick the variable with the minimum ratio of remaining values to degree.
     * @param partialSolution  the partial solution
     * @return one unassigned variable
     */
    private Integer selectUnassignedVariable(Map<Integer, Integer> partialSolution) {
      // Iterate through all the variables in the problem
      for (Integer x : Variables.keySet()) {
        // If it hasn't been assigned to yet, that's our variable!
        if (partialSolution.get(x) == null)
          return x;
      }
      return -1;
    }
    
    /**
     * Backjumping
     * Conflict-directed-backjumping
     * @param partialSolution
     */
    private void jumpBack(Map<Integer, Integer> partialSolution) {
    }
}
