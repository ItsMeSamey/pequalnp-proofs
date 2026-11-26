// Canonicalize the bipartite incidence graph of twelve labels and selected OR wires.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <vector>

using Block = std::uint32_t;
using Palette = std::uint64_t;
using Partition = std::vector<Block>;
using Key = std::vector<Block>;
using Graph = std::array<Block, 24>;

Key canonical_key(const Graph& graph, Partition blocks) {
    while (true) {
        Partition refined;
        for (Block block : blocks) {
            if (std::has_single_bit(block)) {
                refined.push_back(block);
                continue;
            }
            std::map<Key, Block> groups;
            for (Block rest = block; rest; rest &= rest - 1) {
                int vertex = std::countr_zero(rest);
                Key neighbor_counts;
                for (Block color : blocks)
                    neighbor_counts.push_back(std::popcount(graph[vertex] & color));
                groups[neighbor_counts] |= Block{1} << vertex;
            }
            for (auto& [signature, group] : groups)
                refined.push_back(group);
        }
        if (refined.size() == blocks.size())
            break;
        blocks = std::move(refined);
    }

    int selected = -1;
    int smallest = 25;
    for (int i = 0; i < static_cast<int>(blocks.size()); ++i) {
        int size = std::popcount(blocks[i]);
        if (size > 1 && size < smallest) {
            selected = i;
            smallest = size;
        }
    }
    if (selected < 0) {
        Key adjacency;
        for (Block vertex : blocks) {
            Block row = 0;
            for (Block other : blocks)
                row = (row << 1) | static_cast<Block>((graph[std::countr_zero(vertex)] & other) != 0);
            adjacency.push_back(row);
        }
        return adjacency;
    }

    Key best;
    std::set<Block> seen_neighborhoods;
    for (Block rest = blocks[selected]; rest; rest &= rest - 1) {
        int vertex = std::countr_zero(rest);
        // Equal neighborhoods in this block give an explicit transposition automorphism.
        if (!seen_neighborhoods.insert(graph[vertex]).second)
            continue;
        Partition next = blocks;
        Block bit = Block{1} << vertex;
        next[selected] ^= bit;
        next.insert(next.begin() + selected, bit);
        Key key = canonical_key(graph, std::move(next));
        if (best.empty() || key < best)
            best = std::move(key);
    }
    return best;
}

int main(int argc, char** argv) {
    if (argc != 4)
        return 2;
    std::ifstream prefix(argv[1]), palettes(argv[2]);
    std::ofstream output(argv[3]);
    if (!prefix || !palettes || !output)
        throw std::runtime_error("Cannot open prefix, palettes or output");
    std::array<Block, 53> labels{};
    for (int i = 0; i < 24; ++i)
        labels[i] = Block{1} << (i % 12);
    for (int i = 24; i < 53; ++i) {
        int op, left, right;
        if (!(prefix >> op >> left >> right) || op || left < 0 || right < 0 || left >= i || right >= i)
            throw std::runtime_error("Expected an all-OR prefix in topological order");
        labels[i] = labels[left] | labels[right];
    }

    std::set<Key> seen;
    Palette palette;
    int count = 0;
    while (palettes >> palette) {
        if ((palette >> 53) || (palette & ((Palette{1} << 24) - 1)) || std::popcount(palette) > 12)
            throw std::runtime_error("Unexpected normalized palette");
        Graph graph{};
        int vertices = 12;
        for (Palette rest = palette; rest; rest &= rest - 1) {
            Block members = labels[std::countr_zero(rest)];
            graph[vertices] = members;
            for (Block labels_left = members; labels_left; labels_left &= labels_left - 1)
                graph[std::countr_zero(labels_left)] |= Block{1} << vertices;
            ++vertices;
        }
        Block label_vertices = (Block{1} << 12) - 1;
        Block wire_vertices = ((Block{1} << vertices) - 1) ^ label_vertices;
        if (seen.insert(canonical_key(graph, {label_vertices, wire_vertices})).second)
            output << palette << '\n';
        ++count;
    }
    if (!palettes.eof() || !output)
        throw std::runtime_error("Palette input or output failure");
    std::cerr << count << " palettes, " << seen.size() << " incidence classes\n";
}
