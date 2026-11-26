#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

using Word = std::uint64_t;
using Table = std::array<Word, 3>;
using Differences = std::array<Word, 36>;
using Tokens = std::vector<int>;

struct TokenHash {
    std::size_t operator()(const Tokens& values) const {
        Word hash = 31;
        for (int value : values)
            hash = (hash ^ static_cast<Word>(value)) * 0x9e3779b185ebca87ULL;
        return hash;
    }
};

class Search {
    std::vector<Table> values;
    std::vector<Differences> distinguishes;
    std::map<Table, int> identifiers;
    std::unordered_set<Tokens, TokenHash> impossible;
    int target;

    int intern(const Table& table) {
        auto [entry, inserted] = identifiers.emplace(table, static_cast<int>(values.size()));
        if (inserted) {
            values.push_back(table);
            Differences diff{};
            for (int negative = 0; negative < 12; ++negative) {
                int diagonal = 13 * negative;
                if ((table[diagonal / 64] >> (diagonal % 64)) & 1)
                    continue;
                std::copy(table.begin(), table.end(), diff.begin() + 3 * negative);
            }
            distinguishes.push_back(diff);
        }
        return entry->second;
    }

    int compute(int left, int right, int op) {
        Table table;
        for (int k = 0; k < 3; ++k)
            table[k] = op ? (values[left][k] & values[right][k])
                          : (values[left][k] | values[right][k]);
        return intern(table);
    }

    bool merge(Tokens tokens, int copies) {
        std::sort(tokens.begin(), tokens.end());
        if (tokens.size() == 1)
            return tokens.front() == target;
        Tokens key = tokens;
        key.push_back(-1 - copies);
        if (impossible.count(key))
            return false;

        // Count distinguishing tokens up to multiplicity two, in bit-parallel.
        Differences present{}, once{}, twice{};
        for (int token : tokens) {
            for (int k = 0; k < 36; ++k) {
                Word d = distinguishes[token][k];
                twice[k] = (twice[k] & ~d) | (once[k] & d);
                once[k] = (once[k] & ~d) | (d & ~present[k]);
                present[k] |= d;
            }
        }
        for (std::size_t i = 0; i + 1 < tokens.size(); ++i) {
            if (i && tokens[i] == tokens[i - 1])
                continue;
            for (std::size_t j = i + 1; j < tokens.size(); ++j) {
                if (j > i + 1 && tokens[j] == tokens[j - 1])
                    continue;
                int left = tokens[i], right = tokens[j];
                Differences needed;
                for (int k = 0; k < 36; ++k) {
                    Word a = distinguishes[left][k], b = distinguishes[right][k];
                    // Only positive cells in this block need separation from its diagonal.
                    needed[k] = ((once[k] & (a | b)) | (twice[k] & a & b))
                                & values[target][k % 3];
                }
                for (int op : {0, 1}) {
                    int result = compute(left, right, op);
                    bool viable = true;
                    for (int k = 0; k < 36; ++k) {
                        if (needed[k] & ~distinguishes[result][k]) {
                            viable = false;
                            break;
                        }
                    }
                    if (!viable)
                        continue;
                    Tokens next = tokens;
                    next.erase(next.begin() + j);
                    next.erase(next.begin() + i);
                    next.push_back(result);
                    for (int extra = 0; extra <= copies; ++extra) {
                        if (merge(next, copies - extra))
                            return true;
                        next.push_back(result);
                    }
                }
            }
        }
        // Forgetting old unsuccessful states only causes recomputation.
        if (impossible.size() > 1200000)
            impossible.clear();
        impossible.insert(std::move(key));
        return false;
    }

public:
    std::vector<int> wires;

    explicit Search(std::istream& prefix) {
        Table crown{};
        for (int raw = 0; raw < 24; ++raw) {
            Table table{};
            for (int p = 0; p < 144; ++p) {
                Word bit = Word{1} << (p % 64);
                if (p / 12 == raw || 12 + p % 12 == raw)
                    table[p / 64] |= bit;
                if (p / 12 != p % 12)
                    crown[p / 64] |= bit;
            }
            wires.push_back(intern(table));
        }
        target = intern(crown);
        for (int i = 0; i < 29; ++i) {
            int op, a, b;
            if (!(prefix >> op >> a >> b) || (op != 0 && op != 1))
                throw std::runtime_error("Invalid prefix");
            wires.push_back(compute(wires.at(a), wires.at(b), op));
        }
    }

    bool possible(const Tokens& sources, int copies) {
        if (merge(sources, copies))
            return true;
        if (copies == 0)
            return false;
        for (int source : sources) {
            Tokens next = sources;
            next.push_back(source);
            if (possible(next, copies - 1))
                return true;
        }
        return false;
    }
};

int main(int argc, char** argv) {
    if (argc != 2)
        return 2;
    std::ifstream prefix(argv[1]);
    Search search(prefix);
    std::string line;
    int checked = 0;
    while (std::getline(std::cin, line)) {
        std::istringstream fields(line);
        Tokens sources;
        int id;
        while (fields >> id)
            sources.push_back(search.wires.at(id));
        if (!fields.eof() || (sources.size() != 10 && sources.size() != 11))
            throw std::runtime_error("Invalid source set");
        if (search.possible(sources, 12 - static_cast<int>(sources.size()))) {
            std::cerr << "Compatible suffix found for " << line << '\n';
            return 1;
        }
        ++checked;
    }
    std::cout << checked << '\n';
}
