/*
 * CDCL
 * Author : Prateek Kumar
 */

#include <iostream>
#include <vector>
#include <regex>
#include <random>

#define CLAUSE std::vector<int>

// One Assignment in an model
struct Assignment {
	int value;
	int dl;
	int alpha;
	int posFrequency;
	int negFrequency;
	Assignment() : value(0), dl(-1), alpha(-1), posFrequency(0), negFrequency(0)  {}
};

// CNF struct having clauses and assignment
struct CNF {
	int nbvars;
	std::vector<CLAUSE> clauses;
	std::vector<Assignment> model;
	int noOfAssigned;
	CNF() : noOfAssigned(0) {}
};

// Assign literal at decision level dl whose antecedent is alpha
void assign(CNF &cnf, int l, int dl, int alpha) {
	int v = (l > 0) ? l : -l;
	cnf.model[v-1].value = (l > 0) ? 1 : -1;
	cnf.model[v-1].dl = dl;
	cnf.model[v-1].alpha = alpha;
	cnf.noOfAssigned++;
}

// uniPropagate and find conflict
// return kappaAlpha (antecedent of kappa) or -1 for no conflict
int unitPropagate(CNF &cnf, int dl) {
	int nbclauses = cnf.clauses.size();
	// Iterate over all clauses
	for (int i=0; i<nbclauses; i++) {
		int noOfUnassigned = 0;
		int unassigned = 0;
		for (int &l : cnf.clauses[i]) {
			int v = (l > 0) ? l : -l;
			if (cnf.model[v-1].value == 0) {
				noOfUnassigned++; //  Literal is unassigned in this cluase
				unassigned = l; // Current literal that is unassigned
			} else if (cnf.model[v-1].value*l > 0) {
				noOfUnassigned = -1; // Clause is satisfied
				break;
			}
		}
		if (noOfUnassigned == -1) continue;
		if (noOfUnassigned == 1) { // Unit literal so unit propagate
			assign(cnf, unassigned, dl, i);
			i = -1;
		}
		if (noOfUnassigned == 0) { // Conflict so return the clause which was not satisfied
			return i; // This particular clause will be antecedent of kappa
		}
	}
	return -1;
}

std::random_device rd;
std::default_random_engine gen(rd());

// Generate random number between 0..n-1
int genRand(int n) {
	std::uniform_int_distribution<> dis(0, n-1);
	return dis(gen);
}

// Return the unassigned literal with maximum frequency
int maxFreqLit(CNF &cnf) {
	int maxLit = 1;
	int maxFreq = -1;
	for (int i=0; i<cnf.nbvars; i++) { // Check all varibles
		if (cnf.model[i].value == 0) { // If variable is unassigned
			// Check if its frequency is greater than maxFreq
			if (cnf.model[i].posFrequency > maxFreq) {
				maxFreq = cnf.model[i].posFrequency;
				maxLit = (i+1);
			}
			if (cnf.model[i].negFrequency > maxFreq) {
				maxFreq = cnf.model[i].negFrequency;
				maxLit = -(i+1);
			}
		}
	}
	return maxLit;
}

// Pick branching varible
int pickBranchVar(CNF &cnf) {
	int r = genRand(10000);
	// Pick literal with max frequency or randomly
	if (r%20 != 7) return maxFreqLit(cnf);
	if (cnf.noOfAssigned < cnf.nbvars/3) { // If more than 2/3rd is unassigned then assign randomly
		int wcount = 0; // Do not let while loop run for more than nbvars/2 times
		while (wcount < cnf.nbvars/2) {
			int r = genRand(cnf.nbvars);
			if (cnf.model[r].value == 0) {
				if (cnf.model[r].posFrequency > cnf.model[r].negFrequency) return r+1;
				else return -r-1;
			}
			wcount++;
		}
	}
	return maxFreqLit(cnf); // Else pick literal with max frequnecy
}

// Resolve c and b w.r.t. var and store resolved in c
void resolve(CLAUSE &c, CLAUSE &b, int &var) {
	c.insert(c.end(), b.begin(), b.end());
	sort(c.begin(), c.end()); // Sort varibles (required for unique)
	c.erase(unique(c.begin(), c.end()), c.end()); // Erase duplicate literals
	for (unsigned i=0; i<c.size(); i++) { // Erase var and -var from clause
		if (c[i] == var || c[i] == -var) {
			c.erase(c.begin()+i);
			i--;
		}
	}
}

// Perform conflict analysis and back track
int backTrack(CNF &cnf, int &kappaAlpha, int &dl) {
	CLAUSE c = cnf.clauses[kappaAlpha]; // Antecedent of Kappa
	while (true) {
		int assignedAtThisLevel = 0;
		// Find literals with current decison level
		for (int &l : c) {
			int v = (l > 0) ? l : -l;
			if (cnf.model[v-1].dl == dl) assignedAtThisLevel++;
		}
		// If only one literal with current decision level then UIP reached
		if (assignedAtThisLevel == 1) break;
		// Else resolve with a clause which is antecedent of literal of clause in current decision level
		for (int &l : c) {
			int v = (l > 0) ? l : -l;
			int vAlpha = cnf.model[v-1].alpha; //  Antecedent of l
			if (vAlpha == -1 || cnf.model[v-1].dl != dl) continue;
			resolve(c, cnf.clauses[vAlpha], v); // Resolve
			break;
		}
	}
	cnf.clauses.push_back(c); // Learn this clause
	int max = 0;
	for (int &l : c) { // Update frequency count and find jump decision level
		int v = (l > 0) ? l : -l;
		if (l > 0) cnf.model[v-1].posFrequency++;
		if (l < 0) cnf.model[v-1].negFrequency++;
		int d = cnf.model[v-1].dl;
		if (d != dl && d > max) max = d;
	}
	for (Assignment &a : cnf.model) { // Back track by unassigning varibles whose dl > max
		if (a.value != 0 && a.dl > max) {
			cnf.noOfAssigned--;
			a.value = 0;
			a.alpha = -1;
			a.dl = 0;
		}
	}
	return max; // return dl to be backtracked from current dl
}

// Solve cnf using CDCL
bool cdcl(CNF &cnf) {
	if (unitPropagate(cnf, 0) != -1) { // Unitpropagate and return if found conflict
		return false;
	}
	int dl = 0;
	while (cnf.noOfAssigned != cnf.nbvars) { // Until all vars are unassigned
		int var = pickBranchVar(cnf); // Pick branching variable
		dl++; // Increment decision level
		assign(cnf, var, dl, -1); // Assign the branching variable
		while (true) { // Do this until no conflict is found
			int kappaAlpha = unitPropagate(cnf, dl); // Unit propage and find conflict
			// If conflict found and dl is 0 then cnf is unsatisfiable
			if (dl == 0 && kappaAlpha != -1) return false;
			if (kappaAlpha == -1) break; // If No conflict found, break and choose another branching var
			dl = backTrack(cnf, kappaAlpha, dl); // Conflict analysis and back track
		}
	}
	return true; // If all vars assigned then satisfied
}

int main() {
	CNF cnf;
	std::string input_line;
	cnf.nbvars = 0;
	int nbclauses = 0;
	// Take input from stdin
	while (true) {
		std::getline(std::cin, input_line);
		if (input_line.size() == 0 || input_line[0] == 'c') {
			continue;
		}
		std::smatch sm;
		if (std::regex_match(input_line, sm, std::regex("\\s*p\\s+cnf\\s+([0-9]+)\\s+([0-9]+)\\s*"))) {
			cnf.nbvars = std::stoi(sm[1]);
			nbclauses = std::stoi(sm[2]);
		}
		break;
	}
	// Initialize assignments
	for (int i=0; i<cnf.nbvars; i++) {
		Assignment v;
		cnf.model.push_back(v);
	}
	// Take input clauses and maintain literal frequency count
	for (int i=0; i<nbclauses; i++) {
		CLAUSE clause;
		do {
			int in;
			std::cin >> in;
			if (in == 0) break;
			clause.push_back(in);
			if (in > 0) cnf.model[in-1].posFrequency++;
			else if (in < 0) cnf.model[-in-1].negFrequency++;
		} while (true);
		cnf.clauses.push_back(clause);
	}
	// Solve the cnf
	bool sat = cdcl(cnf);
	// Print results
	if (sat) {
		std::cout << "SAT" << std::endl;
		if (cnf.nbvars != 0) {
			std::cout << cnf.model[0].value;
		}
		for (int i=1; i<cnf.nbvars; i++) {
			std::cout << " " << cnf.model[i].value*(i+1);
		}
	} else {
		std::cout << "UNSAT";
	}
	return 0;
}
