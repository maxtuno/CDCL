/*
Copyright (c) 2021 Oscar Riveros. all rights reserved. oscar.riveros@sat-x.io
The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

#include <algorithm>
#include <cassert>
#include <cstring>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <vector>

namespace cdcl {

    template<typename T>
    class solver {

    public:
        bool drat_proof = false;
        bool empty_clause = false; // flag indicates if empty clause is in database

        T status{0};     // -1 = UNSATISFIABLE, 1 = SATISFIABLE, 0 = UNRESOLVED
        T root_level{1}; // root level

        T max_assignment_size{0}; // max_assignment_size for progress purposes

        T number_of_variables{0}; // number of variables
        T number_of_clauses{0};   // number of clauses
        T trail_head{0};          // index of first literal that hasn't been propagated yet

        std::vector<T> unset_variables;  // unset literals
        std::vector<T> trail;            // sequence of assigned literals
        std::vector<T> level_size;       // number of assigned literals up to this level

        std::vector<std::vector<T>> clauses; // database of clauses

        std::map<T, std::vector<T>> watchers; // map literal -> set of clauses watching literal
        std::map<T, bool> analyze_queue;      // map variable -> flag if variable enqueued during conflict analysis

        std::map<T, T> model; // map variable -> currently assigned value
        std::map<T, T> level; // map variable -> level it was set at
        std::map<T, T> cause; // map variable -> clause that caused it to be set

        // watcher frequency heuristic by Oscar Riveros from SAT-X
        std::map<T, T> frequency; // map var -> frequency of occurrence from watches

        std::vector<T> &clause(T &cr) { return clauses[cr - 1]; }

        const std::vector<T> &clause(T &cr) const { return clauses[cr - 1]; }

        bool satisfied(const T &x) { return model[std::abs(x)] == x; }

        bool falsified(const T &x) { return model[std::abs(x)] == -x; }

        bool satisfied(const std::vector<T> &c) {
            return std::any_of(c.begin(), c.end(), [&](auto &x) { return satisfied(x); });
        }

        bool falsified(const std::vector<T> &c) {
            return std::any_of(c.begin(), c.end(), [&](auto &x) { return falsified(x); });
        }

        T current_level() const { return level_size.size(); }

        void new_level() { level_size.push_back(trail.size()); }

        void add_literal(const T &x, const T &clause_id = 0) {
            assert(!falsified(x));
            trail.push_back(x);
            model[std::abs(x)] = x;
            level[std::abs(x)] = current_level();
            cause[std::abs(x)] = clause_id;
            assert(satisfied(x));
        }

        T add_clause(const std::vector<T> &c) {
            if (c.size() == 0) {
                empty_clause = true;
                return 0;
            } else if (c.size() == 1) {
                add_literal(c[0]);
                return 0;
            } else {
                clauses.push_back(c);
                auto cr = clauses.size();
                watchers[c[0]].push_back(cr);
                watchers[c[1]].push_back(cr);
                frequency[std::abs(c[0])]++;
                frequency[std::abs(c[1])]++;
                return cr;
            }
        }

        T select_variable() {
            T x;
            // watcher frequency heuristic by Oscar Riveros from SAT-X
            std::sort(unset_variables.begin(), unset_variables.end(), [&] (auto &a, auto &b) { return frequency[a] < frequency[b]; });
            do {
                if (unset_variables.empty()) {
                    return 0;
                }
                x = unset_variables.back();
                unset_variables.pop_back();
                if (!x) {
                    goto finally;
                }
            } while (model[x]);
            finally:
            return x;
        }

        T propagate(const T &x) {
            T conflict{};
            auto &ws = watchers[-x];
            auto end = ws.end();
            for (auto it = ws.begin(); it != end; ++it) {
                auto cr = *it;
                auto &c = clause(cr);
                // make c[1] a false literal
                if (x == -c[0]) {
                    std::swap(c[0], c[1]);
                }
                assert(x == -c[1]);
                if (satisfied(c[0])) {
                    goto next;
                }
                // find a new watched literal
                for (T i = 2; i < c.size(); i++) {
                    if (!falsified(c[i])) {
                        std::swap(c[1], c[i]);
                        watchers[c[1]].push_back(cr);
                        frequency[std::abs(c[1])]++;
                        std::swap(*it--, *--end);
                        goto next;
                    }
                }
                // conflict or propagate if necessary
                if (falsified(c[0])) {
                    assert(std::all_of(c.begin(), c.end(), [&](T x) { return falsified(x); }));
                    trail_head = trail.size();
                    conflict = cr;
                    break;
                } else {
                    assert(std::all_of(c.begin() + 1, c.end(), [&](T x) { return falsified(x); }));
                    if (!satisfied(c[0])) {
                        add_literal(c[0], cr);
                    }
                }
                next:
                {
                }
            }
            assert(std::all_of(ws.begin(), end, [&](T cr) { return x == -clause(cr)[0] || x == -clause(cr)[1]; }));
            ws.resize(end - ws.begin());
            return conflict;
        }

        T propagate() {
            T conflict{0};
            if (!trail.empty()) {
                do {
                    auto x = trail[trail_head++];
                    conflict = propagate(x);
                } while (trail_head < trail.size() && !conflict);
            }
            return conflict;
        }

        void analyze(T &conflict, std::vector<T> &learnt, T &backtrack_level) {
            auto size = 0;
            T uip{};
            auto i = trail.size() - 1;
            learnt.emplace_back();
            // find UIP and literals from earlier levels
            do {
                for (auto &y : clause(conflict)) {
                    if (uip == y) {
                        continue;
                    }
                    if (!analyze_queue[std::abs(y)] && level[std::abs(y)] > root_level) {
                        analyze_queue[std::abs(y)] = true;
                        if (level[std::abs(y)] >= current_level()) {
                            ++size;
                        } else {
                            learnt.push_back(y);
                        }
                    }
                }
                while (!analyze_queue[std::abs(trail[i])]) {
                    --i;
                }
                uip = trail[i];
                --i;
                conflict = cause[std::abs(uip)];
                analyze_queue[std::abs(uip)] = false;
                --size;
            } while (size > 0);
            learnt[0] = -uip;
            // reset queue
            for (auto &y : learnt) {
                analyze_queue[std::abs(y)] = false;
            }
            // find backtrack level and second watched literal
            if (learnt.size() == 1) {
                backtrack_level = root_level;
            } else {
                auto max = 1;
                backtrack_level = level[std::abs(learnt[max])];
                for (auto j = 2; j != learnt.size(); j++) {
                    if (backtrack_level < level[std::abs(learnt[j])]) {
                        backtrack_level = level[std::abs(learnt[j])];
                        max = j;
                    }
                }
                std::swap(learnt[1], learnt[max]);
            }
        }

        void backtrack(const T &to_level) {
            for (auto it = trail.begin() + level_size[to_level]; it != trail.end(); it++) {
                auto x = std::abs(*it);
                if (std::find(unset_variables.begin(), unset_variables.end(), x) == unset_variables.end()) {
                    unset_variables.emplace_back(x);
                }
                model[x] = 0;
            }
            trail.resize(level_size[to_level]);
            trail_head = trail.size();
            level_size.resize(to_level);
        }

        T solve() {
            max_assignment_size = 0;
            if (empty_clause) {
                status = -1;
                return status;
            }
            for (;;) {
                auto conflict = propagate();
                if (conflict) {
                    if (current_level() == root_level) {
                        status = -1;
                        return status;
                    }
                    T backtrack_level;
                    std::vector<T> learnt;
                    analyze(conflict, learnt, backtrack_level);
                    backtrack(backtrack_level);
                    if (learnt.size() == 1) {
                        add_literal(learnt[0]);
                    } else {
                        auto x = learnt[0];
                        auto cr = add_clause(learnt);
                        add_literal(x, cr);
                    }
                    if (drat_proof) {
                        for (auto &literal : learnt) {
                            std::cout << literal << " ";
                        }
                        std::cout << "0" << std::endl;
                    }
                } else {
                    if (!drat_proof) {
                        if (trail.size() > max_assignment_size) {
                            max_assignment_size = trail.size();
                            std::cout << "\rc " << number_of_variables - max_assignment_size << "    ";
                            std::fflush(stdout);
                        }
                    }
                    auto x = select_variable();
                    if (!x) {
                        status = 1;
                        return status;
                    }
                    new_level();
                    add_literal(-x);
                }
            }
        }

        void load_cnf(std::string &file_name) {
            std::string temporal;
            std::ifstream file(file_name);
            file.seekg(0, std::ifstream::end);
            int length = file.tellg();
            file.seekg(0, std::ifstream::beg);
            char *buffer = new char[length];
            std::cout << "c reading " << length << " characters from " << file_name << std::endl;
            file.read(buffer, length);
            if (file) {
                std::stringstream buffer_stream(buffer);
                for (std::string line; std::getline(buffer_stream, line);) {
                    if (line.front() == 'c') {
                        continue;
                    }
                    std::stringstream line_stream(line);
                    if (line.front() == 'p') {
                        line_stream >> temporal; // p
                        line_stream >> temporal; // cnf
                        line_stream >> number_of_variables;
                        line_stream >> number_of_clauses;
                        level_size.push_back(0);
                        for (int x = 1; x <= number_of_variables; x++) {
                            unset_variables.emplace_back(std::abs(x));
                        }
                        continue;
                    }
                    std::vector<T> literals;
                    while (line_stream.good()) {
                        line_stream >> temporal;
                        if (temporal.front() == '0') {
                            continue;
                        }
                        literals.emplace_back(std::atoi(temporal.c_str()));
                    }
                    if (!literals.empty()) {
                        add_clause(literals);
                    }
                }
            } else {
                throw std::runtime_error("FILE READING ERROR");
            }
            file.close();
            delete[] buffer;
            temporal.clear();
        }
    };

} // namespace cdcl

int main(int argc, char *argv[]) {

    using T = int;

    auto enumerate = false;
    std::string path;

    cdcl::solver<T> solver;

    for (auto i = 1; i < argc; i++) {
        if (!std::strcmp(argv[i], "--all")) {
            enumerate = true;
        } else if (!std::strcmp(argv[i], "--drat-proof")) {
            solver.drat_proof = true;
        } else {
            path = argv[i];
        }
    }
    if (path.empty()) {
        printf("Usage: %s [--all | --drat-proof] <dimacs-format-file.cnf>\n", argv[0]);
        std::exit(EXIT_FAILURE);
    }

    solver.load_cnf(path);

    for (;;) {
        T status = solver.solve();
        printf("\n%sSAT\n", status > 0 ? "" : "UN");
        if (status > 0) {
            for (auto x = 1; x <= solver.number_of_variables; ++x) {
                if (solver.model[std::abs(x)]) {
                    std::cout << solver.model[std::abs(x)] << " ";
                }
            }
            std::cout << "0" << std::endl;
        }
        if (enumerate && status > 0) {
            solver.trail_head = 0;
            std::vector<T> literals;
            for (T x = 1; x <= solver.number_of_variables; x++) {
                if (solver.model[std::abs(x)]) {
                    literals.push_back(-solver.model[std::abs(x)]);
                }
            }
            solver.add_clause(literals);
            continue;
        } else {
            return EXIT_SUCCESS;
        }
    }
}