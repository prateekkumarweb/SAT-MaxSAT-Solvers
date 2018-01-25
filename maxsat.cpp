/*
 * MaxSAT
 * Author : Prateek Kumar
 */

#include <iostream>
#include <vector>
#include "core/Solver.h"

using namespace Minisat;

int main() {
	// Sovlver Object
	Solver S;
	std::string input_line;
	vec<Lit> vars; // All the variables used in the solver
	vec<Lit> auxs; // Auxilliary variable for each clause
	// Take input from stdin
	int nbvars, nbclauses;
	char c;
	while (true) {
		std::cin >> c;
		if (c == 'c') {
			std::getline(std::cin, input_line);
			continue;
		}
		// Take input number of variables and clauses
		if (c == 'p') {
			std::cin >> input_line >> nbvars >> nbclauses;
			break;
		}
	}
	// Initialize variables
	for (int i=0; i<nbvars; i++) {
		Var v = S.newVar();
		vars.push(mkLit(v, false));
	}
	// Take input clauses and add them to the solver with an auxilliary variables stores in auxs vector
	for (int i=0; i<nbclauses; i++) {
		Var v = S.newVar();
		Lit av = mkLit(v, false);
		vec<Lit> c;
		c.push(av); // Add auxilliary variable
		do {
			int in;
			std::cin >> in;
			if (in == 0) break;
			if (in > 0) c.push(vars[in-1]);
			if (in < 0) c.push(~vars[-in-1]);
		} while (true);
		auxs.push(av);
		S.addClause(c); // Add clause to the solver
	}
	Var v = S.newVar();
	Lit av = mkLit(v, false);
	vec<Lit> assumps; // List of assumptions
	// For satisfying all clauses we add all auxialiary variables as mandatory
	for (int i=0; i<nbclauses; i++) {
		S.addClause(av, ~auxs[i]);
	}
	assumps.push(~av);
	bool solved = S.solve(assumps); // Solve for satisfying all variables
	int kValue = 0; // Current kValue
	// kValue is k for which sum auxs[i] <= k, For satisfying all variables k = 0
	// More variables that will be required for sequential encoding
	std::vector<std::vector<Lit> > R;
	for (int i=0; i<nbclauses-1; i++) {
		std::vector<Lit> Ri;
		for (int j=0; j<nbclauses; j++) {
			Var v = S.newVar();
			Lit av = mkLit(v, false);
			Ri.push_back(av);
		}
		R.push_back(Ri);
	}
	// If for kValue = 0, it is unsatisfied then check for different k Values
	if (!solved) {
		// Vary KValue from 1 to nbclauses
		for (int k = 1; k<nbclauses; k++) {
			Var v = S.newVar();
			Lit av = mkLit(v, false); // Assumption variable for for current sum(auxs[i]) <= k
			// Encoding for sum(suxs[i]) <= k
			// Add all clauses required for this encoding
			S.addClause(av, ~auxs[0], R[0][0]);
			for (int j=1; j<k; j++) {
				S.addClause(av, ~R[0][j]);
			}
			for (int i=1; i<nbclauses-1; i++) {
				S.addClause(av, ~auxs[i], R[i][0]);
				S.addClause(av, ~R[i-1][0], R[i][0]);
				for (int j=1; j<k; j++) {
					vec<Lit> c;
					c.push(av);
					c.push(~auxs[i]);
					c.push(~R[i-1][j-1]);
					c.push(R[i][j]);
					S.addClause(c);
					S.addClause(av, ~R[i-1][j], R[i][j]);
				}
				S.addClause(av, ~auxs[i], ~R[i-1][k-1]);
			}
			// for(int i=0; i<nbclauses-1; i++) {
			// 	for (int j=k; j<nbclauses; j++) {
			// 		S.addClause(av, R[i][j]);
			// 	}
			// }
			S.addClause(av, ~auxs[nbclauses-1], ~R[nbclauses-2][k-1]);
			// Encoding ends
			// Change the assumption for previous k
			assumps[k - 1] = ~assumps[k - 1];
			assumps.push(~av); // Assumption for current k
			solved = S.solve(assumps); // Solve for sum(auxs[i]) <= k
			kValue = k; // Update kValue
			if (solved) break; // End the loop if solved
		}
	}
	// Print the number of satisfied clauses
	std::cout << nbclauses - kValue << std::endl;
	// Print the model that satisfies the formula
	for (int i=0; i<nbvars; i++) {
		lbool val = S.model[i];
		if (val == l_True) std::cout << i+1 << " ";
		else if (val == l_False) std::cout << -i-1 << " ";
		else std::cout << i+1 << " ";
	}
	std::cout << 0;
	return 0;
}
