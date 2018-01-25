/*
 * DPLL with Unit Propagation
 * Author : Prateek Kumar
 */

#include <iostream>
#include <string>
#include <regex>
#include <utility>
#include <vector>
#include <algorithm>

#define CLAUSE std::vector<int>
#define CNF std::vector<CLAUSE>

// cnt is array which has counters for each positive literal
// whereas ncnt has counters for each negative literal
int *cnt, *ncnt;
// nbvar - Number of variables, nbcaluses - Number of clauses
int nbvar;
int nbclauses;

// Find index of max in an array
int max(int *array, int n) {
	int mi = 0;
	for (int i=0; i<n; i++) {
		if (array[i] > array[mi]) {
			mi = i;
		}
	}
	return mi;
}

// Returns literal with max counter in cnt and ncnt arrays
int maxcount() {
	int m1 = max(cnt, nbvar);
	int m2 = max(ncnt, nbvar);
	if (cnt[m1] > ncnt[m2]) return m1+1;
	else return -m2-1;
}

// Condition the cnf w.r.t. literal var (modifies original cnf)
void conditionCNF0(CNF &cnf, int var) {
	for (CNF::iterator i = cnf.begin(); i != cnf.end(); i++) {
		CLAUSE::iterator res = find((*i).begin(), (*i).end(), var);
		if (res != (*i).end()) { // Remove the satisfied cluase
			i--;
			cnf.erase(i+1);
			continue;
		}
		res = find((*i).begin(), (*i).end(), -var);
		if (res != (*i).end()) { // Remove literal from cluase where it is false i.e. does not contribute to truthness of clause
			(*i).erase(res);
		}
	}
}

// Condition cnf w.r.t literal var (Creates new cnf)
CNF conditionCNF(CNF &cnf, int var) {
	CNF newcnf;
	std::vector<int>::iterator findRes;
	for (CLAUSE &c : cnf) {
		findRes = find(c.begin(), c.end(), var);
		if (findRes != c.end()) continue; // Ignore satisfied clause
		CLAUSE c1;
		for (int l : c) { // Add all literals in new cluase except its negated form
			if (l != -var) c1.push_back(l);
		}
		newcnf.push_back(c1);
	}
	return newcnf;
}

// Print CNF, used for debugging
void printCNF(CNF &cnf) {
	std::cout << "CNF" << std::endl;
	for (std::vector<int> c : cnf) {
		for (int i : c)
			std::cout << i << " ";
		std::cout << std::endl;
	}
}

// Unit resolution of boolean formula cnf
// v - vector of assigned literals
void unitresolve(CNF &cnf, std::vector<int> &v) {
	bool run = true;
	// Run until all unit clauses are exausted
	while (run) {
		run = false;
		for (CLAUSE c : cnf) {
			if (c.size() == 1) { // If unit clause, then assign it and condition cnf
				run = true;
				conditionCNF0(cnf, c[0]);
				v.push_back(c[0]);
				break;
			}
		}
	}
}

// Solve cnf using DPLL Algorithm
std::pair<bool, std::vector<int>> dpll(CNF &cnf) {
	std::vector<int> model; // Assignment to cnf
	unitresolve(cnf, model); // Unit propagation
	// if cnf is empty then true trivially
	if (cnf.empty()) return std::pair<bool, std::vector<int>>(true, model);
	for (CLAUSE &c : cnf) { // If any clause is empty then false
		if (c.empty()) return std::pair<bool, std::vector<int>>(false, std::vector<int>());
	}
	// Count the literals in the cnf
	for (int i=0; i<nbvar; i++) {
		cnt[i] = ncnt[i] = 0;
	}
	for (CLAUSE &c : cnf) {
		for (int l : c) {
			if (l > 0) cnt[l-1]++;
			else ncnt[-l-1]++;
		}
	}
	// If literal is present in single polarity then assign it
	for (int i=0; i<nbvar; i++) {
		if (ncnt[i] == 0 && cnt[i] > 0) {
			conditionCNF0(cnf, i+1);
			model.push_back(i+1);
			cnt[i] = 0;
		}
		if (cnt[i] == 0 && ncnt[i] > 0) {
			conditionCNF0(cnf, -i-1);
			model.push_back(-i-1);
			ncnt[i] = 0;
		}
	}
	// If cnf is empty then true trivially
	if (cnf.empty()) return std::pair<bool, std::vector<int>>(true, model);
	// If first clause is empty then unsatisfied
	if ((*(cnf.begin())).empty()) return std::pair<bool, std::vector<int>>(false, std::vector<int>());
	int var = maxcount(); // literal with max counter
	CNF c = conditionCNF(cnf, var); // condition on cnf wrt var, create new cnf
	std::pair<bool, std::vector<int>> result = dpll(c); // Run dpll on that
	if (result.first == true) { // If satisfied, then return the model after adding literal var
		result.second.push_back(var);
		result.second.insert(result.second.end(), model.begin(), model.end());
		return result;
	}
	c = conditionCNF(cnf, -var); // condition on cnf wrt -var, create new cnf
	result = dpll(c); // Run dpll on that
	if (result.first == true) { // If satisfied, return the model after adding literal -var
		result.second.push_back(-var);
		result.second.insert(result.second.end(), model.begin(), model.end());
		return result;
	}
	// Return false if not satisfied on either of the assignment
	return std::pair<bool, std::vector<int>>(false, std::vector<int>());
}

int main() {
	// Take input, parse
	std::string input_line;
	nbvar = 0;
	nbclauses = 0;
	while (true) {
		std::getline(std::cin, input_line);
		if (input_line.size() == 0 || input_line[0] == 'c') {
			continue;
		}
		std::smatch sm;
		if (std::regex_match(input_line, sm, std::regex("\\s*p\\s+cnf\\s+([0-9]+)\\s+([0-9]+)\\s*"))) {
			nbvar = std::stoi(sm[1]);
			nbclauses = std::stoi(sm[2]);
		}
		break;
	}
	// Initailize cnf, counters
	CNF cnf;
	cnt = new int[nbvar];
	ncnt = new int[nbvar];
	// Take input clauses
	for (int i=0; i<nbclauses; i++) {
		std::vector<int> clause;
		do {
			int in;
			std::cin >> in;
			if (in == 0) break;
			clause.push_back(in);
		} while (true);
		cnf.push_back(clause);
	}
	// Solve the cnf using DPLL
	std::pair<bool, std::vector<int>> sol =  dpll(cnf);
	if (sol.first) { // If satisfied, print solution
		std::cout << "SAT" << std::endl;
		bool *ans = new bool[nbvar];
		for (std::vector<int>::iterator it = sol.second.begin(); it != sol.second.end(); ++it) {
			if (*it < 0) ans[-*it-1] = false;
			else ans[*it-1] = true;
		}
		if (nbvar != 0) std::cout << (ans[0] ? 1 : -1);
		for (int i=1; i<nbvar; i++) {
			std::cout << " " << (ans[i] ? i+1 : -i-1);
		}
	} else { // If not satisfied, print "UNSAT"
		std::cout << "UNSAT";
	}
	return 0;
}
