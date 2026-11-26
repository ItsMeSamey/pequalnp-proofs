// Necessary inner and outer rectangle conditions for a single repeated signal.
#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

using Palette = std::uint64_t;
using Sources = unsigned;
using Rows = std::bitset<66>;
using Columns = unsigned;
constexpr int source_count = 11;
constexpr Sources full = (1U << source_count) - 1;
struct Cell { int row, column; Sources difference; };
struct Rectangle { Rows rows; Columns columns = 0; };

bool overlaps(const Rectangle& first, const Rectangle& second) {
    return (first.columns & second.columns) && (first.rows & second.rows).any();
}

bool force_cell(std::array<Rectangle, source_count>& hulls, Sources& used,
                Sources choice, int row, int column) {
    Rectangle& hull = hulls[std::countr_zero(choice)];
    Columns column_bit = 1U << column;
    if (hull.rows[row] && (hull.columns & column_bit))
        return true;
    hull.rows.set(row);
    hull.columns |= column_bit;
    for (Sources rest = used & ~choice; rest; rest &= rest - 1)
        if (overlaps(hull, hulls[std::countr_zero(rest)]))
            return false;
    used |= choice;
    return true;
}

std::vector<Sources> extremal(std::vector<Sources> values, bool minimal) {
    std::sort(values.begin(), values.end());
    values.erase(std::unique(values.begin(), values.end()), values.end());
    std::vector<Sources> result;
    for (Sources value : values) {
        bool dominated = false;
        for (Sources other : values)
            if (value != other && (minimal ? !(other & ~value) : !(value & ~other))) {
                dominated = true;
                break;
            }
        if (!dominated)
            result.push_back(value);
    }
    return result;
}

bool possible(Palette palette, const std::array<unsigned, 53>& labels) {
    std::array<Sources, 12> singleton{};
    int position = 0;
    for (Palette rest = palette; rest; rest &= rest - 1, ++position) {
        unsigned bank = labels[std::countr_zero(rest)];
        for (int label = 0; label < 12; ++label)
            if ((bank >> label) & 1U)
                singleton[label] |= 1U << position;
    }
    std::vector<Sources> positives;
    for (int i = 0; i < 12; ++i)
        for (int j = 0; j < i; ++j)
            positives.push_back(singleton[i] | singleton[j]);
    positives = extremal(positives, true);
    auto negatives = extremal({singleton.begin(), singleton.end()}, false);

    std::array<Rows, full + 1> forced_rows{};
    std::array<Columns, full + 1> forced_columns{};
    std::array<Rectangle, source_count> simple{};
    std::vector<Cell> cells;
    for (int i = 0; i < static_cast<int>(positives.size()); ++i) {
        for (int j = 0; j < static_cast<int>(negatives.size()); ++j) {
            Sources diff = positives[i] & ~negatives[j];
            if (!diff)
                return false;
            cells.push_back({i, j, diff});
            forced_rows[diff].set(i);
            forced_columns[diff] |= 1U << j;
            if (std::has_single_bit(diff)) {
                auto& hull = simple[std::countr_zero(diff)];
                hull.rows.set(i);
                hull.columns |= 1U << j;
            }
        }
    }
    std::vector<Sources> conflicts;
    for (int i = 0; i < source_count; ++i)
        for (int j = 0; j < i; ++j)
            if (overlaps(simple[i], simple[j]))
                conflicts.push_back((1U << i) | (1U << j));
    if (conflicts.empty())
        return true;
    std::sort(cells.begin(), cells.end(), [](const Cell& a, const Cell& b) {
        return std::popcount(a.difference) < std::popcount(b.difference);
    });

    // A cell forces inner truth and falsity when its difference lies entirely
    // inside the selected subset. Accumulate its row and column in all supersets.
    for (Sources bit = 1; bit <= full; bit <<= 1)
        for (Sources subset = 0; subset <= full; ++subset)
            if (subset & bit) {
                forced_rows[subset] |= forced_rows[subset ^ bit];
                forced_columns[subset] |= forced_columns[subset ^ bit];
            }

    for (Sources inner = 1; inner < full; ++inner) {
        Sources outer = full ^ inner;
        bool valid = true;
        for (Sources conflict : conflicts)
            if (!(inner & conflict)) {
                valid = false;
                break;
            }
        if (!valid)
            continue;
        Rows can_be_true;
        can_be_true.set();
        Columns can_be_false = (1U << negatives.size()) - 1;
        std::array<Rectangle, source_count> inside{};
        Sources used = 0;
        for (const Cell& cell : cells) {
            Columns column = 1U << cell.column;
            bool row_forced = forced_rows[inner][cell.row];
            bool column_forced = forced_columns[inner] & column;
            Sources choices = cell.difference & inner;
            if (!choices) {
                if (column_forced) can_be_true.reset(cell.row);
                if (row_forced) can_be_false &= ~column;
                if (row_forced && column_forced) {
                    valid = false;
                    break;
                }
            } else if (row_forced && column_forced && std::has_single_bit(choices)
                       && !force_cell(inside, used, choices, cell.row, cell.column)) {
                valid = false;
                break;
            }
        }
        if (!valid)
            continue;
        std::array<Rectangle, source_count> outside{};
        used = 0;
        for (const Cell& cell : cells) {
            // Permit the repeated value as a free choice whenever individually
            // possible. Its two occurrences need no unique-leaf rectangle here.
            if (can_be_true[cell.row] && ((can_be_false >> cell.column) & 1U)
                && (cell.difference & inner))
                continue;
            Sources choices = cell.difference & outer;
            if (!choices || (std::has_single_bit(choices)
                             && !force_cell(outside, used, choices, cell.row, cell.column))) {
                valid = false;
                break;
            }
        }
        if (valid)
            return true;
    }
    return false;
}

int main(int argc, char** argv) {
    if (argc != 4)
        return 2;
    std::ifstream prefix(argv[1]), palettes(argv[2]);
    std::ofstream survivors(argv[3]);
    if (!prefix || !palettes || !survivors)
        throw std::runtime_error("Cannot open prefix, palettes or output");
    std::array<unsigned, 53> labels{};
    for (int i = 0; i < 24; ++i)
        labels[i] = 1U << (i % 12);
    for (int i = 24; i < 53; ++i) {
        int op, left, right;
        if (!(prefix >> op >> left >> right) || op || left < 0 || right < 0 || left >= i || right >= i)
            throw std::runtime_error("Expected an all-OR prefix in topological order");
        labels[i] = labels[left] | labels[right];
    }
    int count = 0, passed = 0;
    Palette palette;
    while (palettes >> palette) {
        if ((palette >> 53) || (palette & ((Palette{1} << 24) - 1))
            || std::popcount(palette) != source_count)
            throw std::runtime_error("Expected eleven distinct normalized sources");
        if (possible(palette, labels)) {
            survivors << palette << '\n';
            ++passed;
        }
        ++count;
    }
    if (!palettes.eof() || !survivors)
        throw std::runtime_error("Palette input or output failure");
    std::cerr << count << " eleven-source classes, " << passed << " survivors\n";
}
