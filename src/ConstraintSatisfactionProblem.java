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
    private int nodesExplored;
    private int constraintsChecked;

    private Map<Integer, Set<Integer>> Variables;
    
    // Let's be real: This is one nasty-looking data structure.
    //    Breakdown: We got a Pair of Variables
    //    This maps to a set of acceptable values of these two variables.
    private Map<hashPair, Set<hashPair>> Constraints;

    private List<Map<Integer, Set<Integer>>> removedLogs;
    private List<Map<Integer, Integer>> addLogs;

    public ConstraintSatisfactionProblem() {
      nodesExplored = 0;
      constraintsChecked = 0;

      Variables = new HashMap<Integer, Set<Integer>>();
      // #gross
      Constraints = new HashMap<hashPair, Set<hashPair>>();

      removedLogs = new ArrayList<HashMap<Integer, Set<Integer>>>();
      addLogs = new ArrayList<HashMap<Integer, Integer>>();

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
        Map<Integer, Integer> solution = backtracking(new HashMap<>());
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
      /* Check if this level of depth has a rLog and aLog yet */
        // If not, create one
        // If so, load it up


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
        Integer x = domainArray[i];

        // Make the assigment
        partialSolution.put(unassignedVar, x);
        /* Add this entry to the aLog */


        // Do the inference (and ensure this won't cause directly awful issues)
        if (inference(unassignedVar, x, partialSolution, depth)) { // Changes partialSolution by reference
          result = backtracking(partialSolution, depth + 1); // Recurse on the updated solution

          // Check for success
          if (result != null) {
            /* We've succeeded! Don't undo anything */
            return result;
          }
        }

        // Undo the changes we just did (but remove x from the domain of unassignedVar)
        this.Variables.get(unassignedVar).remove(x);
        /* Remove this entry from the the aLog */
        /* Remove inference's changes in the rLog and aLog */

        /* Keep the removal of the value we just tried from this var's domain? */
      }

      /* Undo all the changes from this depth level to jump back before returning! */
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
    private boolean inference(Integer var, Integer value, Map<Integer, Integer> partialSolution, int depth) {
      Iterator<hashPair> constraintIter = Constraints.keySet().iterator();
      Set<hashPair> relation; 
      Integer tempVar;
      Iterator<Integer> domainIter;
      Integer potentialVal;
      hashPair tempConstraint;
      Set<Integer> tempDomain;

      // Loop through and remove the new assignment from each domain
      for (Integer x : Variables.keySet()) {
        if (Variables.get(x).remove(value) ) {
          /* mark this as removed in the rLogs */ 
        }
      }

      // Loop through each constraint in the CSP
      for (hashPair scope : Constraints.keySet()) {
        
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

              if (!relation.contains(tempConstraint) ) {
                domainIter.remove();
                /* Mark this as removed in the rLog */
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
            /* Mark this new solution part in aLogs */

            // If this fails in inference, the outer solution is bad too
            // run it at the same depth to keep track of changes
            if (! inference(V, newVal, partialSolution, depth)) {
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
