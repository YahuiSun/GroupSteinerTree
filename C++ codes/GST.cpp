// GST.cpp : This file contains the 'main' function. Program execution begins and ends there.

#include "pch.h"
#include <iostream>
#include <iomanip>
#include <fstream>
#include <ctime>
#include <cstdint>
#include <cstdlib>
#include <numeric>
#include <string>
#include <list>
#include <vector>
#include <tuple>
#include <algorithm>
#include <iterator>
#include <chrono>
#include <queue>
#include <typeinfo>
#include <unordered_set>
#include <unordered_map>
using namespace std;

/*header files in the YS-Graph-Library: https://github.com/YahuiSun/YS-Graph-Library*/
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_minimum_spanning_tree.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_shortest_paths.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_breadth_first_search_a_fixed_number_of_vertices.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_breadth_first_search_a_fixed_number_of_vertices_in_unconnected_graphs_start_from_maxcpn.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_MST_postprocessing.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_distribute_nw_into_ec_evenly.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_copy_weights_of_graph1_to_graph2.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_copy_graph_to_another_graph.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_sum_of_nw_ec.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_merge_graph_hash_of_mixed_weighted.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_connected_components.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_ec_update_pairwise_jaccard_distance.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_nw_ec_normalization.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_extract_subgraph_for_a_list_of_vertices.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_extract_subgraph_for_a_hash_of_vertices.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_generate_random_connected_graph.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_generate_random_groups_of_vertices.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_save_for_GSTP.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_read_for_GSTP.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_BasicProgressive_vertex_edge_weighted.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_DPBF_vertex_edge_weighted.h>
#include <text mining/parse_string.h>
#include <text mining/string_is_number.h>
#include <copy_items.h>
#include <math/ysgraph_math.h>
#include <print_items.h>
#include <subgraph_vector/subgraph_vector.h>




/*header files in the Boost library: https://www.boost.org/*/
#include <boost/random.hpp>
#include <boost/heap/fibonacci_heap.hpp> 





/*algorithms*/

#pragma region
int find_g_min(graph_hash_of_mixed_weighted& group_graph, std::unordered_set<int>& cumpulsory_group_vertices) {

	/*time complexity: O(|T|)*/

	int g_min;
	int g_min_size = INT_MAX;

	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int x = graph_hash_of_mixed_weighted_adjacent_vertices_size(group_graph, *it);
		if (g_min_size > x) {
			g_min_size = x;
			g_min = *it;
		}
	}

	return g_min;

}
#pragma endregion find_g_min

#pragma region
double graph_hash_of_mixed_weighted_lambda_cost(graph_hash_of_mixed_weighted& theta, double lambda) {

	/*time complexity: O(|V|), since theta is a tree; however this function works well if theta is not a tree*/

	double lambda_cost = 0;

	for (auto it1 = theta.hash_of_vectors.begin(); it1 != theta.hash_of_vectors.end(); it1++) {
		int i = it1->first;
		double w_i = it1->second.vertex_weight;
		lambda_cost = lambda_cost + (1 - lambda) * w_i;
		auto search = theta.hash_of_hashs.find(i);
		if (search != theta.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					lambda_cost = lambda_cost + lambda * c_ij;
				}
			}
		}
		else {
			for (auto it2 = it1->second.adj_vertices.begin(); it2 != it1->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					lambda_cost = lambda_cost + lambda * c_ij;
				}
			}
		}

	}

	return lambda_cost;

}
#pragma endregion graph_hash_of_mixed_weighted_lambda_cost

// ENSteiner

#pragma region
void transformation_to_STP(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, graph_hash_of_mixed_weighted& G_t) {

	/*time complexity: O(|V|+|E|+|T||V|)*/

	/*initialization: set M to a large value*/
	double M = 0;
	for (auto it1 = input_graph.hash_of_vectors.begin(); it1 != input_graph.hash_of_vectors.end(); it1++) {
		int i = it1->first;
		double w_i = it1->second.vertex_weight;
		graph_hash_of_mixed_weighted_add_vertex(G_t, i, w_i);
		M = M + w_i;
		auto search = input_graph.hash_of_hashs.find(i);
		if (search != input_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					graph_hash_of_mixed_weighted_add_edge(G_t, i, j, c_ij);
					M = M + c_ij;
				}
			}
		}
		else {
			auto search2 = input_graph.hash_of_vectors.find(i);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					graph_hash_of_mixed_weighted_add_edge(G_t, i, j, c_ij);
					M = M + c_ij;
				}
			}
		}
	}


	/*add dummy vertices and edges*/
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int group_vertex = *it;
		graph_hash_of_mixed_weighted_add_vertex(G_t, group_vertex, 0); // add dummy vertices


		auto search = group_graph.hash_of_hashs.find(group_vertex);
		if (search != group_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int vertex = it2->first;
				graph_hash_of_mixed_weighted_add_edge(G_t, group_vertex, vertex, M); // add dummy edges
			}
		}
		else {
			auto search2 = group_graph.hash_of_vectors.find(group_vertex);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int vertex = it2->first;
				graph_hash_of_mixed_weighted_add_edge(G_t, group_vertex, vertex, M); // add dummy edges
			}
		}
	}

}
#pragma endregion transformation_to_STP

#pragma region
graph_hash_of_mixed_weighted shortest_path_heuristic_1980(graph_hash_of_mixed_weighted& G_t, std::unordered_set<int>& G_t_compulsory_vertices) {

	graph_hash_of_mixed_weighted solu_graph;

	/*start vertex/terminal and add it to solu_graph*/
	int start_vertex = *(G_t_compulsory_vertices.begin());
	double nw = G_t.hash_of_vectors[start_vertex].vertex_weight;
	graph_hash_of_mixed_weighted_add_vertex(solu_graph, start_vertex, nw);


	/*initialize unconnected terminals*/
	std::unordered_set<int> V2;
	for (auto it1 = G_t_compulsory_vertices.begin(); it1 != G_t_compulsory_vertices.end(); it1++) {
		V2.insert(*it1);
	}
	V2.erase(start_vertex);


	/*find SPs from V2 to all the other vertices*/
	std::unordered_map<int, pair<std::unordered_map<int, double>, std::unordered_map<int, int>>> SPs; // <source,pair<distances,predecessors>>
	for (auto it1 = V2.begin(); it1 != V2.end(); it1++) {
		int source = *it1;
		std::unordered_map<int, double> distances;
		std::unordered_map<int, int> predecessors;
		graph_hash_of_mixed_weighted_shortest_paths_source_to_all(G_t, source, distances, predecessors);
		SPs[source] = { distances ,predecessors };
	}


	/*concatinating paths; O(T^2 * V)*/
	while (V2.size() > 0) { // O(|T|)

		int path_V1_end, path_V2_end;
		double path_length = std::numeric_limits<double>::max();

		for (auto it0 = V2.begin(); it0 != V2.end(); it0++) { // O(|T|)
			int unconnected_terminal = *it0;
			for (auto it1 = solu_graph.hash_of_vectors.begin(); it1 != solu_graph.hash_of_vectors.end(); it1++) { // O(|V|)
				int connected_terminal = it1->first;
				double length = SPs[unconnected_terminal].first[connected_terminal];
				if (length < path_length) {
					path_V1_end = connected_terminal;
					path_V2_end = unconnected_terminal;
					path_length = length;
				}
			}
		}

		/*add path; O(|V|)*/
		int v = path_V1_end;
		while (v != path_V2_end) {
			int pre_v = SPs[path_V2_end].second[v];
			double w_v = G_t.hash_of_vectors[v].vertex_weight;
			graph_hash_of_mixed_weighted_add_vertex(solu_graph, v, w_v);
			double w_pre_v = G_t.hash_of_vectors[pre_v].vertex_weight;
			graph_hash_of_mixed_weighted_add_vertex(solu_graph, pre_v, w_pre_v);
			graph_hash_of_mixed_weighted_add_edge(solu_graph, v, pre_v, graph_hash_of_mixed_weighted_edge_weight(G_t, v, pre_v)); 
			v = pre_v;
		}

		V2.erase(path_V2_end);

	}

	return solu_graph;

}
#pragma endregion shortest_path_heuristic_1980

#pragma region
graph_hash_of_mixed_weighted ENSteiner(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices) {

	/*time complexity: O(|T||G_t_E|+|T||G_t_V|log|G_t_V|)*/

	/*transformation_to_STP; time complexity: O(|V|+|E|)*/
	graph_hash_of_mixed_weighted G_t;
	transformation_to_STP(input_graph, group_graph, cumpulsory_group_vertices, G_t); 

	/*time complexity: O(|T||G_t_E|+|T||G_t_V|log|G_t_V|)*/
	graph_hash_of_mixed_weighted theta = shortest_path_heuristic_1980(G_t, cumpulsory_group_vertices);

	/*remove_dummy_components; time complexity: O(|T|), as all terminals in leaves in LANCET solutions*/
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		graph_hash_of_mixed_weighted_remove_vertex(theta, *it);
	}

	return theta;

}
#pragma endregion ENSteiner

// exENSteiner

#pragma region
void transformation_to_NWSTP(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double lambda, graph_hash_of_mixed_weighted& G_t) {

	/*time complexity: O(|V|+|E|+sum{|cumpulsory_groups|})*/

	double M = 0;

	/*initialize M*/
	for (auto it1 = input_graph.hash_of_vectors.begin(); it1 != input_graph.hash_of_vectors.end(); it1++) {
		int i = it1->first;
		double w_i = it1->second.vertex_weight;
		graph_hash_of_mixed_weighted_add_vertex(G_t, i, (1 - lambda) * w_i);
		M = M + (1 - lambda) * w_i;
		auto search = input_graph.hash_of_hashs.find(i);
		if (search != input_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					graph_hash_of_mixed_weighted_add_edge(G_t, i, j, lambda * c_ij);
					M = M + lambda * c_ij;
				}
			}
		}
		else {
			for (auto it2 = it1->second.adj_vertices.begin(); it2 != it1->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					graph_hash_of_mixed_weighted_add_edge(G_t, i, j, lambda * c_ij);
					M = M + lambda * c_ij;
				}
			}
		}

	}

	/*add dummy vertices and edges*/
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int group_vertex = *it;
		graph_hash_of_mixed_weighted_add_vertex(G_t, group_vertex, 0); // add dummy vertices
		auto search = group_graph.hash_of_hashs.find(group_vertex);
		if (search != group_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int vertex = it2->first;
				graph_hash_of_mixed_weighted_add_edge(G_t, group_vertex, vertex, M); // add dummy edges
			}
		}
		else {
			auto search2 = group_graph.hash_of_vectors.find(group_vertex);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int vertex = it2->first;
				graph_hash_of_mixed_weighted_add_edge(G_t, group_vertex, vertex, M); // add dummy edges
			}
		}


	}

}
#pragma endregion transformation_to_NWSTP

#pragma region
void update_G2_ec(graph_hash_of_mixed_weighted& input_graph) {

	/*time complexity: O(|V|+|E|)*/

	for (auto it1 = input_graph.hash_of_vectors.begin(); it1 != input_graph.hash_of_vectors.end(); it1++) {
		int i = it1->first;

		auto search = input_graph.hash_of_hashs.find(i);
		if (search != input_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					double w_i = it1->second.vertex_weight;
					double w_j = input_graph.hash_of_vectors[j].vertex_weight;
					graph_hash_of_mixed_weighted_add_edge(input_graph, i, j, c_ij + w_i / 2 + w_j / 2); // embed nw into ec
				}
			}
		}
		else {
			for (auto it2 = it1->second.adj_vertices.begin(); it2 != it1->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					double w_i = it1->second.vertex_weight;
					double w_j = input_graph.hash_of_vectors[j].vertex_weight;
					graph_hash_of_mixed_weighted_add_edge(input_graph, i, j, c_ij + w_i / 2 + w_j / 2); // embed nw into ec
				}
			}
		}
	}

}
#pragma endregion update_G2_ec

#pragma region
struct node_for_LANCET {
	int source;
	int terminal;
	double priority_value; // distance
}; // define the node in the queue
bool operator<(node_for_LANCET const& x, node_for_LANCET const& y) {
	return x.priority_value > y.priority_value; // < is the max-heap; > is the min heap
}
typedef typename boost::heap::fibonacci_heap<node_for_LANCET>::handle_type handle_t_for_LANCET;

graph_hash_of_mixed_weighted LANCET(graph_hash_of_mixed_weighted& G_t, std::unordered_set<int>& G_t_compulsory_vertices) {

	/*time complexity: O(|T||E|+|T||V|log|V|); G_t contains G_2 edge costs*/

	graph_hash_of_mixed_weighted solu_graph;

	/*random start*/
	/*time complexity: O(|T|) << O(|V|)*/
	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ 0, int(G_t_compulsory_vertices.size() - 1) };
	auto it = G_t_compulsory_vertices.begin();
	int ID = dist(gen);
	for (int i = 0; i < ID; i++) { // i cannot equal ID, or it points to G_t_compulsory_vertices.end(). which is null
		it++;
	}
	int compulsory_vertex = *it;
	std::unordered_set<int> V1, V2;
	V1.insert(compulsory_vertex);
	for (auto it1 = G_t_compulsory_vertices.begin(); it1 != G_t_compulsory_vertices.end(); it1++) {
		V2.insert(*it1);
	}
	V2.erase(compulsory_vertex);

	//print_unordered_set_int(V1);
	//print_unordered_set_int(V2);

	/*find LWP from V2 to all the other vertices;
	time complexity: O(|T||E|+|T||V|log|V|)*/
	std::unordered_map<int, pair<std::unordered_map<int, double>, std::unordered_map<int, int>>>
		LWPs; // <source,pair<distances,predecessors>>
	for (auto it1 = V2.begin(); it1 != V2.end(); it1++) {
		int source = *it1;
		std::unordered_map<int, double> distances;
		std::unordered_map<int, int> predecessors;
		graph_hash_of_mixed_weighted_shortest_paths_source_to_all(G_t, source, distances, predecessors);
		/*dummy node weights in G2 are 0, so you dont need to reimburse dummy node weights into distances here*/
		LWPs[source] = { distances ,predecessors };
	}


	/*push distances between vertices in V2 and vertices in V1 into Q; maximal num of elements: |T|;
	the time complexity of inserting elements for fibonacci_heap is жи(1)*/
	node_for_LANCET node;
	boost::heap::fibonacci_heap<node_for_LANCET> Q;
	std::unordered_map<int, double> Q_keys;
	std::unordered_map<int, handle_t_for_LANCET> Q_handles;
	for (auto it1 = V2.begin(); it1 != V2.end(); it1++) {
		int source = *it1;
		node.source = source;
		node.terminal = compulsory_vertex;
		node.priority_value = LWPs[source].first[compulsory_vertex];
		Q_keys[source] = node.priority_value;
		Q_handles[source] = Q.push(node);
	}

	/*time complexity: O(|T||V|+|T|log|T|);
	at most |T||V| values are checked for Q_keys*/
	while (V2.size() > 0) {

		/*find LWP_min;
		the time complexity of popping elements for fibonacci_heap is O(log n);
		maximal num of elements: |T|*/
		int min_source = Q.top().source, min_terminal = Q.top().terminal;
		V2.erase(min_source); // remove min_source from V2
		Q.pop();

		/*find V_min, E_min; time complexity: O(|V_min||T|);
		min_terminal is in V1, min_source was in V2*/
		int i = min_terminal;
		while (true) {
			graph_hash_of_mixed_weighted_add_vertex(solu_graph, i, 0); // add a v_min to solu_graph
			if (V1.count(i) == 0) { // i is a new element in V1
				double w_i = G_t.hash_of_vectors[i].vertex_weight;
				V1.insert(i); // add a v_min to V1
				for (auto it1 = V2.begin(); it1 != V2.end(); it1++) {
					int source = *it1;
					if (LWPs[source].first[i] + w_i / 2 < Q_keys[source]) { 
						node.source = source;
						node.terminal = i;
						node.priority_value = LWPs[source].first[i] + w_i / 2;
						Q_keys[source] = node.priority_value; 
						Q.update(Q_handles[source], node);
					}
				}
			}
			if (i == LWPs[min_source].second[i]) {
				break;
			}
			else {
				graph_hash_of_mixed_weighted_add_edge(solu_graph, i, LWPs[min_source].second[i],
					graph_hash_of_mixed_weighted_edge_weight(G_t, i, LWPs[min_source].second[i]));  // add a e_min to solu_graph
				//cout << "graph_hash_of_mixed_weighted_add_edge: " << i << " " << LWPs[min_source].second[i] << endl;
			}
			i = LWPs[min_source].second[i]; // i to its predecessor
		}

	}

	return solu_graph;

}
#pragma endregion LANCET

#pragma region
graph_hash_of_mixed_weighted exENSteiner(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double lambda) {

	graph_hash_of_mixed_weighted G_t;
	transformation_to_NWSTP(input_graph, group_graph, cumpulsory_group_vertices, lambda, G_t);

	/*time complexity: O(|V|+|E|)*/
	update_G2_ec(G_t); // both node weights and lambda have been embeded into edge costs 

	/*time complexity: O(|T||G_t_E|+|T||G_t_V|log|G_t_V|)*/
	graph_hash_of_mixed_weighted theta = LANCET(G_t, cumpulsory_group_vertices); // nw and ec in theta are the same with G_t

	/*remove_dummy_components; time complexity: O(|T|), as all terminals in leaves in LANCET solutions*/
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		graph_hash_of_mixed_weighted_remove_vertex(theta, *it);
	}

	/*time complexity O(|V|+|E|)*/
	graph_hash_of_mixed_weighted theta_dash = graph_hash_of_mixed_weighted_MST_postprocessing(input_graph, theta); // nw and ec in theta_dash are the same with input_graph

	return theta_dash;

}
#pragma endregion exENSteiner

// IhlerA

#pragma region
graph_hash_of_mixed_weighted IhlerA(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices) {

	/*time complexity: O(|g_min||E|+|g_min||T||V|+|g_min||V|log|V|);

	note that, the original IhlerA in
	(Ihler, Edmund. "Bounds on the quality of approximate solutions to the group Steiner problem."
	International Workshop on Graph-Theoretic Concepts in Computer Science. Springer, Berlin, Heidelberg, 1990.)
	has mentioned the possibilities of (i) change g_1 to g_min, (ii) return an MST, not any spanning tree of G_i_min.

	Even though the original IhlerA implements Dijkstra's algorithm O(V^2) times, but we can easily see that it just
	needs to implement Dijkstra's algorithm O(V) times*/

	graph_hash_of_mixed_weighted G_i_min;
	double G_i_min_cost = std::numeric_limits<double>::max();

	int g_start = find_g_min(group_graph, cumpulsory_group_vertices); // find g_min

	/*time complexity: O(|g_start|)*/
	std::list<int> g_start_vertices = graph_hash_of_mixed_weighted_adjacent_vertices(group_graph, g_start);

	/*time complexity: O(|g_start||E|+|g_start||T||V|+|g_start||V|log|V|)*/
	for (auto it1 = g_start_vertices.begin(); it1 != g_start_vertices.end(); it1++) {
		int i = *it1;

		graph_hash_of_mixed_weighted G_i;
		double w_i = input_graph.hash_of_vectors[i].vertex_weight;
		graph_hash_of_mixed_weighted_add_vertex(G_i, i, w_i); // in scenarios where the following shortest path is {i}, i cannot be added below

		/*time complexity: O(|E|+|V|log|V|)*/
		std::unordered_map<int, double> distances;
		std::unordered_map<int, int> predecessors;
		graph_hash_of_mixed_weighted_shortest_paths_source_to_all(input_graph, i, distances, predecessors);

		/*time complexity: O(|T||V|)*/
		for (auto it2 = cumpulsory_group_vertices.begin(); it2 != cumpulsory_group_vertices.end(); it2++) { // O(|T|)
			int g = *it2;
			if (g != g_start) {

				/*find SP(i to g); O(|V|) or O(|g|)*/
				int LWP_g_terminal;
				double LWP_g_distance = std::numeric_limits<double>::max();
				std::list<int> g_vertices = graph_hash_of_mixed_weighted_adjacent_vertices(group_graph, g); // O(|V|)
				for (auto it3 = g_vertices.begin(); it3 != g_vertices.end(); it3++) {
					int v = *it3;
					if (distances[v] < LWP_g_distance) {
						LWP_g_distance = distances[v];
						LWP_g_terminal = v;
					}
				}

				/*merge SP(i to g); O(|V|)*/
				while (LWP_g_terminal != predecessors[LWP_g_terminal]) {

					/*add two vertices and an edge (LWP_g_terminal, predecessors[LWP_g_terminal]) into G_i*/
					double w_LWP_g_terminal = input_graph.hash_of_vectors[LWP_g_terminal].vertex_weight;
					graph_hash_of_mixed_weighted_add_vertex(G_i, LWP_g_terminal, w_LWP_g_terminal);
					double w_pre = input_graph.hash_of_vectors[predecessors[LWP_g_terminal]].vertex_weight;
					graph_hash_of_mixed_weighted_add_vertex(G_i, predecessors[LWP_g_terminal], w_pre);
					double ec = graph_hash_of_mixed_weighted_edge_weight(input_graph, LWP_g_terminal, predecessors[LWP_g_terminal]);
					graph_hash_of_mixed_weighted_add_edge(G_i, LWP_g_terminal, predecessors[LWP_g_terminal], ec);

					LWP_g_terminal = predecessors[LWP_g_terminal];
				}
			}
		}

		/*update G_i_min; time complexity: O(|V|)*/
		double G_i_cost = graph_hash_of_mixed_weighted_lambda_cost(G_i, 1); // lambda = 1; only count edge costs
		if (G_i_cost < G_i_min_cost) {
			G_i_min_cost = G_i_cost;
			G_i_min = G_i;
		}

	}

	/*find MST of G_i; time complexity O(|E|+|V|log|V|)*/
	return graph_hash_of_mixed_weighted_MST_postprocessing(input_graph, G_i_min);

}
#pragma endregion IhlerA

// exIhlerA

#pragma region
graph_hash_of_mixed_weighted update_G2_lambda(graph_hash_of_mixed_weighted& input_graph, double lambda) {

	/*time complexity: O(|V|+|E|);
	it outputs a new graph, does not change input_graph;
	vertex weights in G_2 are the same with those in input_graph*/

	graph_hash_of_mixed_weighted G_2;

	for (auto it1 = input_graph.hash_of_vectors.begin(); it1 != input_graph.hash_of_vectors.end(); it1++) {
		int i = it1->first;
		double w_i = it1->second.vertex_weight;
		auto search = input_graph.hash_of_hashs.find(i);
		if (search != input_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					double w_j = input_graph.hash_of_vectors[j].vertex_weight;
					double new_c_ij = lambda * c_ij + (1 - lambda) * (w_i / 2 + w_j / 2);
					graph_hash_of_mixed_weighted_add_edge(G_2, i, j, new_c_ij); // embed nw into ec
				}
			}
		}
		else {
			for (auto it2 = it1->second.adj_vertices.begin(); it2 != it1->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					double w_j = input_graph.hash_of_vectors[j].vertex_weight;
					double new_c_ij = lambda * c_ij + (1 - lambda) * (w_i / 2 + w_j / 2);
					graph_hash_of_mixed_weighted_add_edge(G_2, i, j, new_c_ij); // embed nw into ec
				}
			}
		}
	}

	return G_2;

}
#pragma endregion update_G2_lambda

#pragma region
graph_hash_of_mixed_weighted exIhlerA(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double lambda) {

	/*G_2 is for finding lowest-weight paths*/
	graph_hash_of_mixed_weighted G_2 = update_G2_lambda(input_graph, lambda);

	graph_hash_of_mixed_weighted G_i_min;
	double G_i_min_cost = std::numeric_limits<double>::max();

	/*time complexity: O(|T|)*/
	int g_min = find_g_min(group_graph, cumpulsory_group_vertices);

	/*time complexity: O(|g_min|)*/
	std::list<int> g_min_vertices = graph_hash_of_mixed_weighted_adjacent_vertices(group_graph, g_min);


	/*time complexity: O(|g_min||E|+|g_min||T||V|+|g_min||V|log|V|)*/
	for (auto it1 = g_min_vertices.begin(); it1 != g_min_vertices.end(); it1++) {
		int i = *it1;

		graph_hash_of_mixed_weighted G_i;
		double w_i = input_graph.hash_of_vectors[i].vertex_weight;
		graph_hash_of_mixed_weighted_add_vertex(G_i, i, w_i); // in scenarios where the following shortest path is {i}, i cannot be added below

		/*time complexity: O(|E|+|V|log|V|)*/
		std::unordered_map<int, double> distances;
		std::unordered_map<int, int> predecessors;
		graph_hash_of_mixed_weighted_shortest_paths_source_to_all(G_2, i, distances, predecessors);

		/*time complexity: O(|T||V|)*/
		for (auto it2 = cumpulsory_group_vertices.begin(); it2 != cumpulsory_group_vertices.end(); it2++) { // O(|T|)
			int g = *it2;
			if (g != g_min) {

				/*find SP(i to g); O(|V|) or O(|g|)*/
				int LWP_g_terminal;
				double LWP_g_distance = std::numeric_limits<double>::max();
				std::list<int> g_vertices = graph_hash_of_mixed_weighted_adjacent_vertices(group_graph, g); // O(|V|)
				for (auto it3 = g_vertices.begin(); it3 != g_vertices.end(); it3++) {
					int v = *it3;
					if (distances[v] < LWP_g_distance) {
						LWP_g_distance = distances[v];
						LWP_g_terminal = v;
					}
				}

				/*merge SP(i to g); O(|V|)*/
				while (LWP_g_terminal != predecessors[LWP_g_terminal]) {

					/*add two vertices and an edge (LWP_g_terminal, predecessors[LWP_g_terminal]) into G_i*/
					double w_LWP_g_terminal = input_graph.hash_of_vectors[LWP_g_terminal].vertex_weight;
					graph_hash_of_mixed_weighted_add_vertex(G_i, LWP_g_terminal, w_LWP_g_terminal);
					double w_pre = input_graph.hash_of_vectors[predecessors[LWP_g_terminal]].vertex_weight;
					graph_hash_of_mixed_weighted_add_vertex(G_i, predecessors[LWP_g_terminal], w_pre);
					double ec = graph_hash_of_mixed_weighted_edge_weight(input_graph, LWP_g_terminal, predecessors[LWP_g_terminal]);
					graph_hash_of_mixed_weighted_add_edge(G_i, LWP_g_terminal, predecessors[LWP_g_terminal], ec);

					LWP_g_terminal = predecessors[LWP_g_terminal];
				}
			}
		}

		/*update G_i_min; time complexity: O(|V|)*/
		double G_i_cost = graph_hash_of_mixed_weighted_lambda_cost(G_i, lambda); 
		if (G_i_cost < G_i_min_cost) {
			G_i_min_cost = G_i_cost;
			G_i_min = G_i;
		}

	}


	return graph_hash_of_mixed_weighted_MST_postprocessing(input_graph, G_i_min);

}
#pragma endregion exIhlerA


// FastAPP

#pragma region
pair<std::unordered_map<int, double>, std::unordered_map<int, int>> find_LWPs_to_g(graph_hash_of_mixed_weighted& group_graph, graph_hash_of_mixed_weighted& G_2, int g_vertex, double lambda) {

	/*time complexity: O(|V|+|E|)*/

	/*add dummy vertex and edges; time complexity: O(|V|)*/
	graph_hash_of_mixed_weighted_add_vertex(G_2, g_vertex, 0); // add dummy vertex
	auto search = group_graph.hash_of_hashs.find(g_vertex);
	if (search != group_graph.hash_of_hashs.end()) {
		for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
			int vertex = it2->first; // vertex is in group g_vertex

			double nw = G_2.hash_of_vectors[vertex].vertex_weight; // vertex weights in G_2 are the same with those in input_graph
			double dummy_ec = (1 - lambda) * nw / 2; // original dummy edge weight is 0, this is the weight embedded with vertex weights
			graph_hash_of_mixed_weighted_add_edge(G_2, g_vertex, vertex, dummy_ec); // add dummy edge

		}
	}
	else {
		auto search2 = group_graph.hash_of_vectors.find(g_vertex); // if v is not in g, error is here
		for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
			int vertex = it2->first; // vertex is in group g_vertex

			double nw = G_2.hash_of_vectors[vertex].vertex_weight; // vertex weights in G_2 are the same with those in input_graph
			double dummy_ec = (1 - lambda) * nw / 2; // original dummy edge weight is 0, this is the weight embedded with vertex weights
			graph_hash_of_mixed_weighted_add_edge(G_2, g_vertex, vertex, dummy_ec); // add dummy edge

		}
	}

	/*time complexity: O(|E|+|V|log|V|)*/
	std::unordered_map<int, double> distances;
	std::unordered_map<int, int> predecessors;
	graph_hash_of_mixed_weighted_shortest_paths_source_to_all(G_2, g_vertex, distances, predecessors); /*time complexity: O(|V|+|E|)*/
	graph_hash_of_mixed_weighted_remove_vertex(G_2, g_vertex);  // all dummy vertex and edges are removed; time complexity: O(|V|)
	distances.erase(g_vertex);
	predecessors.erase(g_vertex);
	for (auto it = distances.begin(); it != distances.end(); it++) {
		int v = it->first;
		double nw = G_2.hash_of_vectors[v].vertex_weight; // vertex weights in G_2 are the same with those in input_graph
		it->second = it->second + (1 - lambda) * nw / 2; // update the distance to be the regulated weight of the LWP from v to g_vertex
	}
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		int pre = it->second;
		if (pre == g_vertex) {
			it->second = it->first; // since g_vertex is not in predecessors, it->second points to it->first, i.e., the path ends at it->first.
		}
	}

	return { distances, predecessors };

}
#pragma endregion find_LWPs_to_g

#pragma region
struct node_for_removeleaf {
	int index;
	double priority_value; // distance
}; // define the node in the queue
bool operator<(node_for_removeleaf const& x, node_for_removeleaf const& y) {
	return x.priority_value < y.priority_value; // < is the max-heap; > is the min heap
}

bool this_is_a_non_unique_group_leaf(graph_hash_of_mixed_weighted& theta_dash,
	std::unordered_map<int, std::unordered_set<int>>& groups_and_sets_of_vertices,
	std::unordered_map<int, std::unordered_set<int>>& vertices_and_sets_of_groups, int v) {

	/*time complexity O(|T|)*/

	if (graph_hash_of_mixed_weighted_adjacent_vertices_size(theta_dash, v) != 1) { // v is not a leaf
		return false;
	}

	for (auto it = vertices_and_sets_of_groups[v].begin(); it != vertices_and_sets_of_groups[v].end(); it++) {
		int group = *it;
		if (groups_and_sets_of_vertices[group].size() == 1) {
			return false;
		}
	}

	return true;

}

void remove_non_unique_group_leaves(graph_hash_of_mixed_weighted& theta_dash, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double lambda) {

	/*time complexity O(|T||V|+|V|log|V|)*/

	/*time complexity O(|T||V|)*/
	std::unordered_map<int, std::unordered_set<int>> groups_and_sets_of_vertices, vertices_and_sets_of_groups;
	for (auto it = theta_dash.hash_of_vectors.begin(); it != theta_dash.hash_of_vectors.end(); it++) {
		int v = it->first;
		vertices_and_sets_of_groups[v] = {};
	}
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int group = *it;
		groups_and_sets_of_vertices[group] = {};
	}
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int group = *it;

		auto search = group_graph.hash_of_hashs.find(group);
		if (search != group_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int v = it2->first;
				if (theta_dash.hash_of_vectors.count(v) > 0) {
					groups_and_sets_of_vertices[group].insert(v);
					vertices_and_sets_of_groups[v].insert(group);
				}
			}
		}
		else {
			auto search2 = group_graph.hash_of_vectors.find(group);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int v = it2->first;
				if (theta_dash.hash_of_vectors.count(v) > 0) {
					groups_and_sets_of_vertices[group].insert(v);
					vertices_and_sets_of_groups[v].insert(group);
				}
			}
		}
	}


	node_for_removeleaf node;
	boost::heap::fibonacci_heap<node_for_removeleaf> Q;

	/*push non_unique_group leaves into Q; time complexity O(|T||V|)*/
	for (auto it = theta_dash.hash_of_vectors.begin(); it != theta_dash.hash_of_vectors.end(); it++) {
		int leaf = (*it).first;

		auto search = theta_dash.hash_of_hashs.find(leaf);
		if (search != theta_dash.hash_of_hashs.end()) {
			if (search->second.size() == 1) {  // a leaf
				if (this_is_a_non_unique_group_leaf(theta_dash, groups_and_sets_of_vertices, vertices_and_sets_of_groups, leaf)) {
					std::list<pair<int, double>> x = graph_hash_of_mixed_weighted_adjacent_vertices_and_weights(theta_dash, leaf);
					int adj_v = x.front().first;
					double ec = x.front().second;
					double w_leaf = it->second.vertex_weight;

					node.index = leaf;
					node.priority_value = (1 - lambda) * w_leaf + lambda * ec;
					Q.push(node);
				}

			}
		}
		else {
			if (it->second.adj_vertices.size() == 1) {  // a leaf
				if (this_is_a_non_unique_group_leaf(theta_dash, groups_and_sets_of_vertices, vertices_and_sets_of_groups, leaf)) {
					std::list<pair<int, double>> x = graph_hash_of_mixed_weighted_adjacent_vertices_and_weights(theta_dash, leaf);
					int adj_v = x.front().first;
					double ec = x.front().second;
					double w_leaf = it->second.vertex_weight;

					node.index = leaf;
					node.priority_value = (1 - lambda) * w_leaf + lambda * ec;
					Q.push(node);
				}

			}
		}
	}

	/*time complexity O(|T||V|+|V|log|V|)*/
	while (Q.size() > 0) {

		int top_leaf = Q.top().index;
		Q.pop(); /*time complexity O(|V|log|V|)*/

		if (this_is_a_non_unique_group_leaf(theta_dash, groups_and_sets_of_vertices, vertices_and_sets_of_groups, top_leaf)) {
			std::list<int> x = graph_hash_of_mixed_weighted_adjacent_vertices(theta_dash, top_leaf);
			int adj = x.front();
			graph_hash_of_mixed_weighted_remove_vertex(theta_dash, top_leaf); // remove this leaf

			/*update groups_and_sets_of_vertices, vertices_and_sets_of_groups*/
			/*time complexity O(|T|)*/
			for (auto it = vertices_and_sets_of_groups[top_leaf].begin();
				it != vertices_and_sets_of_groups[top_leaf].end(); it++) {
				int group = *it;
				groups_and_sets_of_vertices[group].erase(top_leaf);
			}
			vertices_and_sets_of_groups.erase(top_leaf);

			if (this_is_a_non_unique_group_leaf(theta_dash, groups_and_sets_of_vertices,
				vertices_and_sets_of_groups, adj)) { // adj is a new non_unique_group_leaf

				std::list<pair<int, double>> y = graph_hash_of_mixed_weighted_adjacent_vertices_and_weights(theta_dash, adj);

				int adj_adj = y.front().first;
				double ec = y.front().second;
				double w_adj = theta_dash.hash_of_vectors[adj].vertex_weight;

				node.index = adj;
				node.priority_value = (1 - lambda) * w_adj + lambda * ec;
				Q.push(node);
			}

		}

	}


}
#pragma endregion remove_non_unique_group_leaves

#pragma region
graph_hash_of_mixed_weighted FastAPP(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double lambda) {

	/*time complexity: O(|T||E|+|T||V|log|V|)*/

	/*time complexity: O(|V|+|E|)*/
	graph_hash_of_mixed_weighted G_2 = update_G2_lambda(input_graph, lambda);

	/*time complexity: O(|T||E|+|T||V|log|V|)*/
	std::unordered_map<int, pair<std::unordered_map<int, double>, std::unordered_map<int, int>>> LWPs_to_groups;
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int g_vertex = *it;
		LWPs_to_groups[g_vertex] = find_LWPs_to_g(group_graph, G_2, g_vertex, lambda);
	}
	//G_2.clear();

	int g_min = find_g_min(group_graph, cumpulsory_group_vertices); // find g_min
	//cout << "g_min=" << g_min << endl;


	int v_min;
	double cost_v_min = INT_MAX;
	/*time complexity: O(|T||V|)*/
	auto search = group_graph.hash_of_hashs.find(g_min);
	if (search != group_graph.hash_of_hashs.end()) {
		for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) { /*time complexity: O(|V|)*/
			int vertex = it2->first; // vertex is in group g_min

			double max_LWP_weight = 0;
			for (auto it = LWPs_to_groups.begin(); it != LWPs_to_groups.end(); it++) { /*time complexity: O(|T|); there is no need to skip g_min here, since LWP_weight for g_min is 0*/
				double LWP_weight = it->second.first[vertex]; // we assume that graph is connected, otherwise vertex may not be in these indexes
				if (max_LWP_weight < LWP_weight) {
					max_LWP_weight = LWP_weight;
				}
			}
			if (cost_v_min > max_LWP_weight) {
				v_min = vertex;
				cost_v_min = max_LWP_weight;
			}

		}
	}
	else {
		auto search2 = group_graph.hash_of_vectors.find(g_min); // if v is not in g, error is here
		for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
			int vertex = it2->first; // vertex is in group g_min

			double max_LWP_weight = 0;
			for (auto it = LWPs_to_groups.begin(); it != LWPs_to_groups.end(); it++) { /*time complexity: O(|T|)*/
				double LWP_weight = it->second.first[vertex]; // we assume that graph is connected, otherwise vertex may not be in these indexes
				if (max_LWP_weight < LWP_weight) {
					max_LWP_weight = LWP_weight;
				}
			}
			if (cost_v_min > max_LWP_weight) {
				v_min = vertex;
				cost_v_min = max_LWP_weight;
			}

		}
	}
	//cout << "v_min=" << v_min << endl;




	/*build G_min; time complexity: O(|T||V|)*/
	std::unordered_set<int> G_min; // a hash of vertices
	for (auto it = LWPs_to_groups.begin(); it != LWPs_to_groups.end(); it++) { /*time complexity: O(|T|)*/
		int g_vertex = it->first;
		if (g_vertex != g_min) {
			/*merge LWP(v_min to g_vertex) into G_min; O(|V|)*/
			G_min.insert(v_min);
			int pre = it->second.second[v_min]; // it->second.second is the predecessor index
			while (v_min != pre) {
				G_min.insert(pre);
				v_min = pre;
				pre = it->second.second[v_min];
			}

		}
	}

	/*time complexity: O(|E|+|V|log|V|+|T||V|)*/
	graph_hash_of_mixed_weighted theta = graph_hash_of_mixed_weighted_MST_postprocessing_hash_of_vertices(input_graph, G_min);
	//remove_non_unique_group_leaves(theta, group_graph, cumpulsory_group_vertices, lambda);

	return theta;

}

graph_hash_of_mixed_weighted fastAPP2(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double lambda) {

	/*time complexity: O(|T||E|+|T||V|log|V|)*/

	/*time complexity: O(|V|+|E|)*/
	graph_hash_of_mixed_weighted G_2 = update_G2_lambda(input_graph, lambda);

	/*time complexity: O(|T||E|+|T||V|log|V|)*/
	std::unordered_map<int, pair<std::unordered_map<int, double>, std::unordered_map<int, int>>> LWPs_to_groups;
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int g_vertex = *it;
		LWPs_to_groups[g_vertex] = find_LWPs_to_g(group_graph, G_2, g_vertex, lambda);
	}

	int g_min = find_g_min(group_graph, cumpulsory_group_vertices); // find g_min
	//cout << "g_min=" << g_min << endl;


	int v_min;
	double cost_v_min = INT_MAX;
	/*time complexity: O(|T||V|)*/
	auto search = group_graph.hash_of_hashs.find(g_min);
	if (search != group_graph.hash_of_hashs.end()) {
		for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) { /*time complexity: O(|V|)*/
			int vertex = it2->first; // vertex is in group g_min

			double sum_LWP_weight = 0;
			for (auto it = LWPs_to_groups.begin(); it != LWPs_to_groups.end(); it++) { /*time complexity: O(|T|); there is no need to skip g_min here, since LWP_weight for g_min is 0*/
				double LWP_weight = it->second.first[vertex]; // we assume that graph is connected, otherwise vertex may not be in these indexes
				sum_LWP_weight = sum_LWP_weight + LWP_weight;
			}
			if (cost_v_min > sum_LWP_weight) {
				v_min = vertex;
				cost_v_min = sum_LWP_weight;
			}

		}
	}
	else {
		auto search2 = group_graph.hash_of_vectors.find(g_min); // if v is not in g, error is here
		for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
			int vertex = it2->first; // vertex is in group g_min

			double sum_LWP_weight = 0;
			for (auto it = LWPs_to_groups.begin(); it != LWPs_to_groups.end(); it++) { /*time complexity: O(|T|); there is no need to skip g_min here, since LWP_weight for g_min is 0*/
				double LWP_weight = it->second.first[vertex]; // we assume that graph is connected, otherwise vertex may not be in these indexes
				sum_LWP_weight = sum_LWP_weight + LWP_weight;
			}
			if (cost_v_min > sum_LWP_weight) {
				v_min = vertex;
				cost_v_min = sum_LWP_weight;
			}

		}
	}




	/*build G_min; time complexity: O(|T||V|)*/
	std::unordered_set<int> G_min; // a hash of vertices
	for (auto it = LWPs_to_groups.begin(); it != LWPs_to_groups.end(); it++) { /*time complexity: O(|T|)*/
		int g_vertex = it->first;
		if (g_vertex != g_min) {
			/*merge LWP(v_min to g_vertex) into G_min; O(|V|)*/
			G_min.insert(v_min);
			int pre = it->second.second[v_min]; // it->second.second is the predecessor index
			while (v_min != pre) {
				G_min.insert(pre);
				v_min = pre;
				pre = it->second.second[v_min];
			}

		}
	}

	/*time complexity: O(|E|+|V|log|V|+|T||V|)*/
	graph_hash_of_mixed_weighted theta = graph_hash_of_mixed_weighted_MST_postprocessing_hash_of_vertices(input_graph, G_min);
	//remove_non_unique_group_leaves(theta, group_graph, cumpulsory_group_vertices, lambda);

	return theta;

}
#pragma endregion fastAPP


// ImprovAPP

#pragma region
struct node_ImprovAPP {
	int connected_v;
	int unconncected_g;
	double priority_value;
}; // define the node in the queue
bool operator<(node_ImprovAPP const& x, node_ImprovAPP const& y) {
	return x.priority_value > y.priority_value; // < is the max-heap; > is the min heap
}
typedef typename boost::heap::fibonacci_heap<node_ImprovAPP>::handle_type handle_t_ImprovAPP;

void ImprovAPP_iteration_process(int v, int g_min, std::unordered_set<int>& cumpulsory_group_vertices, double lambda,
	graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& theta_min, double& cost_theta_min,
	std::unordered_map<int, pair<std::unordered_map<int, double>, std::unordered_map<int, int>>>& LWPs_to_groups) {

	/*time complexity: O(|T|(|V|+log|T|))*/

	/*initialization; time complexity: O(|T|)*/
	std::unordered_set<int> V_c, Gamma_uc;
	V_c.insert(v);
	for (auto it1 = cumpulsory_group_vertices.begin(); it1 != cumpulsory_group_vertices.end(); it1++) {
		Gamma_uc.insert(*it1);
	}
	Gamma_uc.erase(g_min);
	graph_hash_of_mixed_weighted theta_v;
	node_ImprovAPP node;
	boost::heap::fibonacci_heap<node_ImprovAPP> Q;
	std::unordered_map<int, double> Q_keys;
	std::unordered_map<int, handle_t_ImprovAPP> Q_handles;


	/*push LWPs into Q; time complexity: O(|T|)*/
	for (auto it1 = Gamma_uc.begin(); it1 != Gamma_uc.end(); it1++) {
		node.connected_v = v;
		node.unconncected_g = *it1;
		node.priority_value = LWPs_to_groups[*it1].first[v];
		Q_keys[*it1] = node.priority_value;
		Q_handles[*it1] = Q.push(node);

	}


	/*time complexity: O(|T||V|+|T|log|T|)*/
	while (Gamma_uc.size() > 0) {

		int v_top = Q.top().connected_v, g_top = Q.top().unconncected_g;
		Q.pop(); // time complexity: O(log|T|)

		std::unordered_set<int> V_newc;

		/*merge LWP into theta_v; time complexity: O(|V|)*/
		double v_top_weight = input_graph.hash_of_vectors[v_top].vertex_weight;
		graph_hash_of_mixed_weighted_add_vertex(theta_v, v_top, v_top_weight);
		int pre = LWPs_to_groups[g_top].second[v_top]; // LWPs_to_groups[g_top].second is the predecessor index
		while (v_top != pre) {
			double pre_weight = input_graph.hash_of_vectors[pre].vertex_weight;
			graph_hash_of_mixed_weighted_add_vertex(theta_v, pre, pre_weight);
			V_newc.insert(pre); // pre is a newly connected vertex
			V_c.insert(pre); // pre is a newly connected vertex
			double ec = graph_hash_of_mixed_weighted_edge_weight(input_graph, v_top, pre);
			graph_hash_of_mixed_weighted_add_edge(theta_v, v_top, pre, ec);
			v_top = pre;
			pre = LWPs_to_groups[g_top].second[v_top];
		}
		Gamma_uc.erase(g_top); // update Gamma_uc


		/*update LWPs in Q; time complexity: O(|T||V|) throught the whole loop*/
		for (auto it = V_newc.begin(); it != V_newc.end(); it++) {
			int new_v = *it;
			for (auto it1 = Gamma_uc.begin(); it1 != Gamma_uc.end(); it1++) {
				int g = *it1;
				double new_v_to_g_weight = LWPs_to_groups[g].first[new_v];
				if (new_v_to_g_weight < Q_keys[g]) {
					node.connected_v = new_v;
					node.unconncected_g = g;
					node.priority_value = new_v_to_g_weight;
					Q_keys[g] = new_v_to_g_weight;
					Q.update(Q_handles[g], node); // O(1), since it's decrease key
				}
			}
		}
	}

	/*update theta_min; time complexity: O(|V|)*/
	double cost_theta_v = graph_hash_of_mixed_weighted_lambda_cost(theta_v, lambda);
	if (cost_theta_v < cost_theta_min) {
		cost_theta_min = cost_theta_v;
		theta_min = theta_v;
	}

}
#pragma endregion ImprovAPP_iteration_process

#pragma region
graph_hash_of_mixed_weighted ImprovAPP(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double lambda) {

	/*time complexity: O(|T||E|+|T||V|log|V| + |g_min||T|(|V|+log|T|))*/

	/*time complexity: O(|V|+|E|)*/
	graph_hash_of_mixed_weighted G_2 = update_G2_lambda(input_graph, lambda);

	/*time complexity: O(|T||E|+|T||V|log|V|)*/
	std::unordered_map<int, pair<std::unordered_map<int, double>, std::unordered_map<int, int>>> LWPs_to_groups;
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int g_vertex = *it;
		LWPs_to_groups[g_vertex] = find_LWPs_to_g(group_graph, G_2, g_vertex, lambda);
		//cout << "LWPs_to_groups[" << g_vertex << "]:" << endl;
		//print_unordered_map_int_double(LWPs_to_groups[g_vertex].first);
		//print_unordered_map_int_int(LWPs_to_groups[g_vertex].second);
	}
	

	int g_min = find_g_min(group_graph, cumpulsory_group_vertices); // find g_min
	//cout << "g_min=" << g_min << endl;


	graph_hash_of_mixed_weighted theta_min;
	double cost_theta_min = INT_MAX;
	/*time complexity: O(|g_min||T|(|V|+log|T|))*/
	auto search = group_graph.hash_of_hashs.find(g_min);
	if (search != group_graph.hash_of_hashs.end()) {
		for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) { /*time complexity: O(|V|)*/
			int v = it2->first; // vertex is in group g_min

			/*time complexity: O(|T|(|V|+log|T|))*/
			ImprovAPP_iteration_process(v, g_min, cumpulsory_group_vertices, lambda, input_graph, theta_min, cost_theta_min, LWPs_to_groups);
		}
	}
	else {
		auto search2 = group_graph.hash_of_vectors.find(g_min); // if v is not in g, error is here
		for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
			int v = it2->first; // vertex is in group g_min

			/*time complexity: O(|T|(|V|+log|T|))*/
			ImprovAPP_iteration_process(v, g_min, cumpulsory_group_vertices, lambda, input_graph, theta_min, cost_theta_min, LWPs_to_groups);
		}
	}
	//cout << "v_min=" << v_min << endl;





	/*update MST; time complexity: O(|E|+|V|log|V|)*/
	std::unordered_set<int> G_min; // a hash of vertices
	for (auto it = theta_min.hash_of_vectors.begin(); it != theta_min.hash_of_vectors.end(); it++) {
		G_min.insert(it->first);
	}
	theta_min = graph_hash_of_mixed_weighted_MST_postprocessing_hash_of_vertices(input_graph, G_min);


	/*time complexity O(|T||V|+|V|log|V|)*/
	remove_non_unique_group_leaves(theta_min, group_graph, cumpulsory_group_vertices, lambda);



	/*time complexity: O(|V|)*/
	return theta_min;

}
#pragma endregion ImprovAPP


// PartialOPT

#pragma region
graph_hash_of_mixed_weighted PartialOPT(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double lambda, int h) {

	graph_hash_of_mixed_weighted theta_dashdash;
	double theta_dashdash_lambda_cost = std::numeric_limits<double>::max();

	/*time complexity: O(|T|)*/
	int g_min = find_g_min(group_graph, cumpulsory_group_vertices);

	/*time complexity: O(|g_min|)*/
	std::list<int> g_min_vertices = graph_hash_of_mixed_weighted_adjacent_vertices(group_graph, g_min);

	/*time complexity: O(|g_min|^2|E|+|g_min|^2|T-h||V|+|g_min|^2|V|log|V| + |g_min|DPBF(T to h) )*/
	for (auto it1 = g_min_vertices.begin(); it1 != g_min_vertices.end(); it1++) {
		int i = *it1;

		std::unordered_set<int> G_i_vertices;

		/*time complexity: O(|T|)*/
		std::unordered_set<int> Gamma_dash, Gamma_dashdash;
		for (auto it2 = cumpulsory_group_vertices.begin(); it2 != cumpulsory_group_vertices.end(); it2++) {
			int g = *it2;
			if (g != g_min) {
				if (Gamma_dash.size() < h - 1) {
					Gamma_dash.insert(g);
				}
				else {
					Gamma_dashdash.insert(g);
				}
			}
		}
		graph_hash_of_mixed_weighted_add_vertex(group_graph, INT_MAX, 0); // a new group vertex for {i}
		graph_hash_of_mixed_weighted_add_edge(group_graph, INT_MAX, i, 1); // i is in this new group
		Gamma_dash.insert(INT_MAX);
		Gamma_dashdash.insert(INT_MAX);

		/*time complexity: O(DPBF(T to h))*/
		graph_hash_of_mixed_weighted theta_h = graph_hash_of_mixed_weighted_DPBF_vertex_edge_weighted(input_graph, group_graph, Gamma_dash, lambda);
		for (auto it2 = theta_h.hash_of_vectors.begin(); it2 != theta_h.hash_of_vectors.end(); it2++) {
			int v = it2->first;
			G_i_vertices.insert(v);
		}

		/*time complexity: O(|g_min||E|+|g_min||T-h||V|+|g_min||V|log|V|)*/
		graph_hash_of_mixed_weighted theta_Gamma;
		if (Gamma_dashdash.size() > 1) {
			theta_Gamma = exIhlerA(input_graph, group_graph, Gamma_dashdash, lambda);
		}
		else { // theta_Gamma only contains i
			graph_hash_of_mixed_weighted_add_vertex(theta_Gamma, i, 1);			
		}
		for (auto it2 = theta_Gamma.hash_of_vectors.begin(); it2 != theta_Gamma.hash_of_vectors.end(); it2++) {
			int v = it2->first;
			G_i_vertices.insert(v);
		}

		graph_hash_of_mixed_weighted_remove_vertex(group_graph, INT_MAX); //remove the new group {i}

		/*time complexity O(|E|+|V|log|V|)*/
		graph_hash_of_mixed_weighted theta_dashdash_i = graph_hash_of_mixed_weighted_MST_postprocessing_hash_of_vertices(input_graph, G_i_vertices);

		/*time complexity O(|T||V|+|V|log|V|)*/
		remove_non_unique_group_leaves(theta_dashdash_i, group_graph, cumpulsory_group_vertices, lambda);

		/*time complexity: O(|V|)*/
		if (graph_hash_of_mixed_weighted_lambda_cost(theta_dashdash_i, lambda) < theta_dashdash_lambda_cost) {
			theta_dashdash_lambda_cost = graph_hash_of_mixed_weighted_lambda_cost(theta_dashdash_i, lambda);
			theta_dashdash = theta_dashdash_i;
		}

	}

	return theta_dashdash;

}
#pragma endregion PartialOPT



// Guha_16103_algorithm

#pragma region
graph_hash_of_mixed_weighted generate_G2(graph_hash_of_mixed_weighted& input_graph) {

	/*time complexity: O(|V|+|E|)*/

	graph_hash_of_mixed_weighted G2;

	/*initialization*/
	for (auto it1 = input_graph.hash_of_vectors.begin(); it1 != input_graph.hash_of_vectors.end(); it1++) {
		int i = it1->first;
		graph_hash_of_mixed_weighted_add_vertex(G2, i, 0); // no node weights in G2

		auto search = input_graph.hash_of_hashs.find(i);
		if (search != input_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					double w_i = it1->second.vertex_weight;
					double w_j = input_graph.hash_of_vectors[j].vertex_weight;
					graph_hash_of_mixed_weighted_add_edge(G2, i, j, c_ij + w_i / 2 + w_j / 2); // embed nw into ec
				}
			}
		}
		else {
			for (auto it2 = it1->second.adj_vertices.begin(); it2 != it1->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					double w_i = it1->second.vertex_weight;
					double w_j = input_graph.hash_of_vectors[j].vertex_weight;
					graph_hash_of_mixed_weighted_add_edge(G2, i, j, c_ij + w_i / 2 + w_j / 2); // embed nw into ec
				}
			}
		}
	}

	return G2;

}
#pragma endregion generate_G2

#pragma region 
struct node_for_minimum_ratio_spider {
	int min_distance_tree_ID;
	int v_terminal;
	double priority_value; // distance
}; // define the node in the queue
bool operator<(node_for_minimum_ratio_spider const& x, node_for_minimum_ratio_spider const& y) {
	return x.priority_value > y.priority_value; // < is the max-heap; > is the min heap
}

void find_minimum_ratio_spider(std::unordered_map<int, pair<std::unordered_map<int, double>, std::unordered_map<int, int>>>&
	LWPs, graph_hash_of_mixed_weighted& G_t, std::unordered_map<int, graph_hash_of_mixed_weighted>& terminal_trees,
	pair<int, list<pair<int, int>>>& minimum_spider, pair<int, list<pair<int, int>>>& minimum_spider3,
	double& minimum_ratio, double& minimum_ratio_spider3) {

	/*find a spider wih the minimum ratio; see Klein and Ravi 1995 paper*/
	/*time complexity: O(|V|^2 + |V||T|log|T|)*/

	minimum_ratio = std::numeric_limits<double>::max();
	minimum_ratio_spider3 = std::numeric_limits<double>::max();

	//pair<int, list<pair<int, int>>> minimum_spider; // <root, list<pair<terminal_tree_ID, end_v>>>

	//pair<int, list<pair<int, int>>> minimum_spider3; // <root, list<pair<terminal_tree_ID, end_v>>>


	/*time complexity: O(|V|^2 + |V||T|log|T|)*/
	for (auto it1 = G_t.hash_of_vectors.begin(); it1 != G_t.hash_of_vectors.end(); it1++) {

		int start_v = it1->first; // find a spider rooted at start_v
		double start_v_nw = it1->second.vertex_weight;

		//cout << "find_minimum_ratio_spider check start_v: " << start_v << endl;

		pair<int, list<pair<int, int>>> spider, spider3;
		spider.first = start_v;

		/*time complexity: O(|V|)*/
		boost::heap::fibonacci_heap<node_for_minimum_ratio_spider> Q_min_distances_to_terminal_trees;
		node_for_minimum_ratio_spider node;
		for (auto it2 = terminal_trees.begin(); it2 != terminal_trees.end(); it2++) {
			int tree_ID = it2->first;
			int v_terminal;
			double min_distance = std::numeric_limits<double>::max();
			for (auto it3 = terminal_trees[tree_ID].hash_of_vectors.begin(); it3 != terminal_trees[tree_ID].hash_of_vectors.end(); it3++) {
				int v_end = it3->first; // a vertex in terminal_trees[tree_ID]
				if (min_distance > LWPs[start_v].first[v_end]) {
					min_distance = LWPs[start_v].first[v_end]; // distance from start_v to v_end in this tree
					v_terminal = v_end;
				}
			}
			node.min_distance_tree_ID = tree_ID;
			node.v_terminal = v_terminal;
			node.priority_value = min_distance;
			Q_min_distances_to_terminal_trees.push(node);
		}

		double minimum_ratio_for_v, minimum_ratio_for_v_spider3;

		/*connect the closest two terminal_trees*/
		node = Q_min_distances_to_terminal_trees.top();
		Q_min_distances_to_terminal_trees.pop();
		int tree_ID1 = node.min_distance_tree_ID;
		int end_v1 = node.v_terminal;
		double dis1 = node.priority_value;
		node = Q_min_distances_to_terminal_trees.top();
		Q_min_distances_to_terminal_trees.pop();
		int tree_ID2 = node.min_distance_tree_ID;
		int end_v2 = node.v_terminal;
		double dis2 = node.priority_value;
		minimum_ratio_for_v = (start_v_nw + dis1 + dis2) / 2;
		spider.second.push_back({ tree_ID1 , end_v1 });
		spider.second.push_back({ tree_ID2 , end_v2 });

		//cout << "tree_ID1: " << tree_ID1 << " end_v1: " << end_v1 << " tree_ID2: " << tree_ID2 << " end_v2: "
		//	<< end_v2 << " minimum_ratio_for_v: " << minimum_ratio_for_v << endl;


		/*time complexity: O(|T|log|T|)*/
		while (Q_min_distances_to_terminal_trees.size() > 0) { // check all the terminal_trees from the closest

			node = Q_min_distances_to_terminal_trees.top();
			Q_min_distances_to_terminal_trees.pop();
			int tree_ID1 = node.min_distance_tree_ID;
			int end_v1 = node.v_terminal;
			double dis1 = node.priority_value;

			double new_ratio = ((minimum_ratio_for_v * spider.second.size()) + dis1) / (spider.second.size() + 1);

			//cout << "tree_ID1: " << tree_ID1 << " end_v1: " << end_v1 << " dis1: " << dis1 << " new_ratio: "
			//	<< new_ratio << endl;

			if (new_ratio < minimum_ratio_for_v) { // it's profitable to add connect new terminal_tree
				minimum_ratio_for_v = new_ratio;
				spider.second.push_back({ tree_ID1 , end_v1 });
				if (Q_min_distances_to_terminal_trees.size() == 0) {
					minimum_ratio_for_v_spider3 = minimum_ratio_for_v;
					spider3 = spider;
				}
			}
			else { // it's not profitable to add connect new terminal_tree
				if (spider.second.size() == 2) {
					minimum_ratio_for_v_spider3 = new_ratio;
					spider3 = spider;
					spider3.second.push_back({ tree_ID1 , end_v1 });
				}
				else {
					minimum_ratio_for_v_spider3 = minimum_ratio_for_v;
					spider3 = spider;
				}
				break;
			}
		}

		if (minimum_ratio > minimum_ratio_for_v) {
			minimum_ratio = minimum_ratio_for_v;
			minimum_spider = spider;
		}
		if (minimum_ratio_spider3 > minimum_ratio_for_v_spider3) {
			minimum_ratio_spider3 = minimum_ratio_for_v_spider3;
			minimum_spider3 = spider3;
			//cout << "minimum_ratio_spider3:" << minimum_ratio_spider3 << endl;
		}

	}

}
#pragma endregion find_minimum_ratio_spider 

#pragma region 
void contract_minimum_ratio_spider(std::unordered_map<int, pair<std::unordered_map<int, double>,
	std::unordered_map<int, int>>>&
	LWPs, graph_hash_of_mixed_weighted& G_t, std::unordered_map<int, graph_hash_of_mixed_weighted>& terminal_trees,
	pair<int, list<pair<int, int>>>& minimum_spider) {


	/*time complexity: O(|V|+|E|)*/

	// contract all trees to contract_terminal_tree_ID
	int contract_terminal_tree_ID = minimum_spider.second.begin()->first; // the 1st terminal_tree in this spider

	int start_v = minimum_spider.first;
	for (auto it1 = minimum_spider.second.begin(); it1 != minimum_spider.second.end(); it1++) {
		int tree_ID = (*it1).first;
		int end_v = (*it1).second;

		/*contract terminal_trees[tree_ID] to terminal_trees[contract_terminal_tree_ID]*/
		if (tree_ID != contract_terminal_tree_ID) {
			graph_hash_of_mixed_weighted_copy_graph_to_another_graph
			(terminal_trees[contract_terminal_tree_ID], terminal_trees[tree_ID]);
		}
		terminal_trees.erase(tree_ID);

		/*contract path[start_v, end_v] to terminal_trees[contract_terminal_tree_ID]*/
		int prede = LWPs[start_v].second[end_v];
		while (1 > 0) {
			graph_hash_of_mixed_weighted_add_vertex(terminal_trees[contract_terminal_tree_ID],
				end_v, G_t.hash_of_vectors[end_v].vertex_weight);
			graph_hash_of_mixed_weighted_add_vertex(terminal_trees[contract_terminal_tree_ID],
				prede, G_t.hash_of_vectors[prede].vertex_weight);
			if (prede != end_v) {
				graph_hash_of_mixed_weighted_add_edge(terminal_trees[contract_terminal_tree_ID],
					end_v, prede, graph_hash_of_mixed_weighted_edge_weight(G_t, end_v, prede));
			}
			else {
				break;
			}
			end_v = prede;
			prede = LWPs[start_v].second[end_v];
		}

	}

}


#pragma endregion contract_minimum_ratio_spider

#pragma region 
list<pair<pair<int, int>, pair<double, pair<int, int >>>> find_lowest_paths_between_terminal_trees(
	std::unordered_map<int, pair<std::unordered_map<int, double>, std::unordered_map<int, int>>>&
	LWPs, graph_hash_of_mixed_weighted& G_t, std::unordered_map<int, graph_hash_of_mixed_weighted>& terminal_trees) {

	/*time complexity: O(|V|^2)*/

	list<pair<pair<int, int>, pair<double, pair<int, int >>>> paths;
	// pair<pair<tree_ID1,tree_ID2>,pair<distance,pair<start_v,end_v>>>


	for (auto it1 = terminal_trees.begin(); it1 != terminal_trees.end(); it1++) {
		int tree_ID1 = it1->first;
		for (auto it2 = terminal_trees.begin(); it2 != terminal_trees.end(); it2++) {
			int tree_ID2 = it2->first;
			if (tree_ID1 < tree_ID2) {
				int start_v, end_v;
				double min_distance = std::numeric_limits<double>::max();
				for (auto it3 = it1->second.hash_of_vectors.begin(); it3 != it1->second.hash_of_vectors.end(); it3++) {
					int v1 = it3->first; // vertex in tree_ID1
					for (auto it4 = it2->second.hash_of_vectors.begin(); it4 != it2->second.hash_of_vectors.end(); it4++) {
						int v2 = it4->first; // vertex in tree_ID2
						if (LWPs[v1].first[v2] < min_distance) {
							min_distance = LWPs[v1].first[v2];
							start_v = v1;
							end_v = v2;
						}
					}
				}
				paths.push_back({ {tree_ID1, tree_ID2}, {min_distance, {start_v,end_v}} });
			}
		}
	}

	return paths;

}
#pragma endregion find_lowest_paths_between_terminal_trees

#pragma region 
void contract_terminal_tree2_to_terminal_tree1_by_the_lowest_path(
	std::unordered_map<int, pair<std::unordered_map<int, double>, std::unordered_map<int, int>>>&
	LWPs, graph_hash_of_mixed_weighted& G_t, std::unordered_map<int, graph_hash_of_mixed_weighted>& terminal_trees,
	int tree_ID1, int tree_ID2) {


	int start_v, end_v;
	double min_distance = std::numeric_limits<double>::max();
	for (auto it3 = terminal_trees[tree_ID1].hash_of_vectors.begin(); it3 != terminal_trees[tree_ID1].hash_of_vectors.end(); it3++) {
		int v1 = it3->first; // vertex in tree_ID1
		for (auto it4 = terminal_trees[tree_ID2].hash_of_vectors.begin(); it4 != terminal_trees[tree_ID2].hash_of_vectors.end(); it4++) {
			int v2 = it4->first; // vertex in tree_ID2
			if (LWPs[v1].first[v2] < min_distance) {
				min_distance = LWPs[v1].first[v2];
				start_v = v1;
				end_v = v2;
			}
		}
	}

	graph_hash_of_mixed_weighted_copy_graph_to_another_graph(terminal_trees[tree_ID1], terminal_trees[tree_ID2]);
	terminal_trees.erase(tree_ID2);

	int prede = LWPs[start_v].second[end_v];
	while (1 > 0) {
		graph_hash_of_mixed_weighted_add_vertex(terminal_trees[tree_ID1], end_v, G_t.hash_of_vectors[end_v].vertex_weight);
		graph_hash_of_mixed_weighted_add_vertex(terminal_trees[tree_ID1], prede, G_t.hash_of_vectors[prede].vertex_weight);
		if (prede != end_v) {
			graph_hash_of_mixed_weighted_add_edge(terminal_trees[tree_ID1], end_v, prede, graph_hash_of_mixed_weighted_edge_weight(G_t, end_v, prede));
		}
		else {
			break;
		}
		end_v = prede;
		prede = LWPs[start_v].second[end_v];
	}

}
#pragma endregion contract_terminal_tree1_to_terminal_tree2_by_the_lowest_path

#pragma region 
graph_hash_of_mixed_weighted Guha_16103_algorithm(graph_hash_of_mixed_weighted& G_t,
	std::unordered_set<int>& G_t_compulsory_vertices, graph_hash_of_mixed_weighted& G2) {

	/*we assume that node weights of compulsory_vertices are zero*/

	graph_hash_of_mixed_weighted solution_graph;

	/*time complexity: O(|T|)*/
	std::unordered_map<int, graph_hash_of_mixed_weighted> terminal_trees;
	for (auto it = G_t_compulsory_vertices.begin(); it != G_t_compulsory_vertices.end(); it++) {
		int terminal = *it;
		graph_hash_of_mixed_weighted tree;
		graph_hash_of_mixed_weighted_add_vertex(tree, terminal, G_t.hash_of_vectors[terminal].vertex_weight); // each terminal is a terminal_tree initially
		terminal_trees[terminal] = tree;
	}

	/*find LWPs from all vertices to all vertices;
	time complexity: O(|V||E|+|V|^2log|V|)*/
	std::unordered_map<int, pair<std::unordered_map<int, double>, std::unordered_map<int, int>>>
		LWPs; // <source,pair<distances,predecessors>>
	for (auto it1 = G_t.hash_of_vectors.begin(); it1 != G_t.hash_of_vectors.end(); it1++) {
		int source = it1->first;
		std::unordered_map<int, double> distances;
		std::unordered_map<int, int> predecessors;
		graph_hash_of_mixed_weighted_shortest_paths_source_to_all(G2, source, distances, predecessors);
		/*node weights in G2 are 0, so you dont need to reimburse node weights into distances*/
		LWPs[source] = { distances ,predecessors };
		// if weights of compulsory vertices are 0, then distances do not include costs of end points
	}

	while (terminal_trees.size() > 2) { // if there are only two terminal trees left, then connect them optimally


		//cout << "terminal_trees.size():" << terminal_trees.size() << endl;
		//for (auto it = terminal_trees.begin(); it != terminal_trees.end(); it++) {
		//	cout << "terminal_trees [" << it->first << "]:" << endl;
		//	graph_hash_of_mixed_weighted_print(it->second);
		//}
		//getchar();


		pair<int, list<pair<int, int>>> minimum_spider; // <root, list<pair<terminal_tree_ID, end_v>>>
		pair<int, list<pair<int, int>>> minimum_spider3; // <root, list<pair<terminal_tree_ID, end_v>>>
		double minimum_ratio = std::numeric_limits<double>::max();
		double minimum_ratio_spider3 = std::numeric_limits<double>::max();

		/*time complexity: O(|V|^2 + |V||T|log|T|)*/
		find_minimum_ratio_spider(LWPs, G_t, terminal_trees, minimum_spider, minimum_spider3, minimum_ratio, minimum_ratio_spider3);

		//cout << "minimum_ratio:" << minimum_ratio << endl;
		//cout << "minimum_spider.first:" << minimum_spider.first << endl;
		//cout << "minimum_spider.second.size():" << minimum_spider.second.size() << endl;
		//for (auto it = minimum_spider.second.begin(); it != minimum_spider.second.end(); it++) {
		//	cout << "minimum_spider.second pair [" << it->first << "," << it->second << "]:" << endl;
		//}
		//cout << "minimum_ratio_spider3:" << minimum_ratio_spider3 << endl;
		//cout << "minimum_spider3.first:" << minimum_spider3.first << endl;
		//cout << "minimum_spider3.second.size():" << minimum_spider3.second.size() << endl;
		//for (auto it = minimum_spider3.second.begin(); it != minimum_spider3.second.end(); it++) {
		//	cout << "minimum_spider3.second pair [" << it->first << "," << it->second << "]:" << endl;
		//}

		if (minimum_spider.second.size() >= 3) { // contract a 3+ spider: minimum_ratio_spidering_tree_num
			/*time complexity: O(|V|+|E|)*/
			contract_minimum_ratio_spider(LWPs, G_t, terminal_trees, minimum_spider);
		}
		else {

			/*time complexity: O(|V|^2)*/
			list<pair<pair<int, int>, pair<double, pair<int, int >>>> paths = find_lowest_paths_between_terminal_trees(
				LWPs, G_t, terminal_trees);
			// pair<pair<tree_ID1,tree_ID2>,pair<distance,pair<start_v,end_v>>>

			double bound = min_double({ (double)(8 * minimum_ratio / 3), (double)(2 * minimum_ratio_spider3) });

			//for (auto it = paths.begin(); it != paths.end(); it++) {
			//	cout << "paths < <" << it->first.first << "," << it->first.second << ">, <"
			//		<< it->second.first  << ", <" << it->second.second.first <<"," 
			//		<< it->second.second.second << "> > >" << endl;
			//}
			//cout << "bound:" << bound << endl;


			graph_hash_of_mixed_weighted T;
			int l_i = 0;
			for (auto it = paths.begin(); it != paths.end(); it++) {
				double distance = it->second.first;
				if (distance <= bound) {
					l_i++;
					int start_v = it->second.second.first;
					int end_v = it->second.second.second;
					int prede = LWPs[start_v].second[end_v];
					while (1 > 0) {
						graph_hash_of_mixed_weighted_add_vertex(T, end_v, G_t.hash_of_vectors[end_v].vertex_weight);
						graph_hash_of_mixed_weighted_add_vertex(T, prede, G_t.hash_of_vectors[prede].vertex_weight);
						if (prede != end_v) {
							graph_hash_of_mixed_weighted_add_edge(T, end_v, prede, graph_hash_of_mixed_weighted_edge_weight(G_t, end_v, prede));
						}
						else {
							break;
						}
						end_v = prede;
						prede = LWPs[start_v].second[end_v];
					}
				}
			}

			double cost_T = graph_hash_of_mixed_weighted_sum_of_nw_ec(T);



			double value1 = cost_T / (-log(1 - (double)l_i / terminal_trees.size()));
			double value2 = 2 * terminal_trees.size() * minimum_ratio;
			double value3 = (double)3 / 2 * terminal_trees.size() * minimum_ratio_spider3;


			//cout << "cost_T:" << cost_T << endl;
			//cout << "graph_hash_of_mixed_weighted_print(T): " << endl;
			//graph_hash_of_mixed_weighted_print(T);
			//cout << "l_i:" << l_i << endl;
			//cout << "terminal_trees.size():" << terminal_trees.size() << endl;
			//cout << "value1:" << value1 << endl;
			//cout << "value2:" << value2 << endl;
			//cout << "value3:" << value3 << endl;


			if (value1 == min_double({ value1, value2, value3 })) {
				/*contract the forest of terminal_trees induced by paths*/
				std::unordered_map<int, int> contracted_terminal_trees; // <contracted_tree, larger_tree>
				for (auto it = paths.begin(); it != paths.end(); it++) {
					double distance = it->second.first;
					if (distance <= bound) {
						int tree_ID1 = it->first.first;
						int tree_ID2 = it->first.second;
						if (contracted_terminal_trees.count(tree_ID1) > 0) {
							while (contracted_terminal_trees.count(tree_ID1) > 0) {
								tree_ID1 = contracted_terminal_trees[tree_ID1];
							}
						}
						if (contracted_terminal_trees.count(tree_ID2) > 0) {
							while (contracted_terminal_trees.count(tree_ID2) > 0) {
								tree_ID2 = contracted_terminal_trees[tree_ID2];
							}
						}
						if (tree_ID1 != tree_ID2) {
							contract_terminal_tree2_to_terminal_tree1_by_the_lowest_path(
								LWPs, G_t, terminal_trees, tree_ID1, tree_ID2);
							contracted_terminal_trees[tree_ID2] = tree_ID1;

							//cout << "contract terminal_tree[" << tree_ID2 << "] to terminal_tree[" << tree_ID1 << "]" << endl;
							//cout << "terminal_trees.size():" << terminal_trees.size() << endl;
							//for (auto it = terminal_trees.begin(); it != terminal_trees.end(); it++) {
							//	cout << "terminal_trees [" << it->first << "]:" << endl;
							//	graph_hash_of_mixed_weighted_print(it->second);
							//}

						}
					}
				}
			}
			else if (value2 == min_double({ value1, value2, value3 })) {
				/*contract the minimum_spider*/
				/*time complexity: O(|V|+|E|)*/
				contract_minimum_ratio_spider(LWPs, G_t, terminal_trees, minimum_spider);
			}
			else {
				/*contract the minimum_spider3*/
				/*time complexity: O(|V|+|E|)*/
				contract_minimum_ratio_spider(LWPs, G_t, terminal_trees, minimum_spider3);
			}

		}

	}


	//cout << "after contraction terminal_trees.size():" << terminal_trees.size() << endl;


	if (terminal_trees.size() == 2) {
		auto it = terminal_trees.begin();
		int tree_ID1 = it->first;
		it++;
		int tree_ID2 = it->first;
		contract_terminal_tree2_to_terminal_tree1_by_the_lowest_path(
			LWPs, G_t, terminal_trees, tree_ID1, tree_ID2);
	}



	return terminal_trees.begin()->second;

}
#pragma endregion Guha_16103_algorithm 








/*experiments*/

#pragma region
graph_hash_of_mixed_weighted produce_small_group_graph(std::unordered_set<int>& queried_group_vertices,
	graph_hash_of_mixed_weighted& subgraph_g, graph_hash_of_mixed_weighted& group_graph, bool& this_subgraph_is_feasible) {

	graph_hash_of_mixed_weighted subgraph_group_graph;

	std::unordered_set<int> covered_groups;


	for (auto it = queried_group_vertices.begin(); it != queried_group_vertices.end(); it++) {
		int g = *it;
		graph_hash_of_mixed_weighted_add_vertex(subgraph_group_graph, g, 0);
	}
	for (auto it = subgraph_g.hash_of_vectors.begin(); it != subgraph_g.hash_of_vectors.end(); it++) {
		int v = it->first;
		graph_hash_of_mixed_weighted_add_vertex(subgraph_group_graph, v, 0);
		for (auto it1 = queried_group_vertices.begin(); it1 != queried_group_vertices.end(); it1++) {
			int g = *it1;
			if (graph_hash_of_mixed_weighted_contain_edge(group_graph, v, g)) {
				graph_hash_of_mixed_weighted_add_edge(subgraph_group_graph, v, g, 0);
				covered_groups.insert(g);
			}
		}
	}

	if (covered_groups.size() == queried_group_vertices.size()) {
		this_subgraph_is_feasible = true;
	}
	else {
		this_subgraph_is_feasible = false;
	}

	return subgraph_group_graph;
}
#pragma endregion produce_small_group_graph

#pragma region
std::unordered_set<int> sample_random_skill_vertices(int sample_num,
	std::unordered_set<int>& skill_vertices) {

	/*randomly select a start_skill_vertex from skill_vertices;
		  time complexity: O(sample_num|skill_vertices|)*/

	if (sample_num > skill_vertices.size()) {
		cout << "Error: sample_num > skill_vertices.size() in sample_random_skill_vertices" << endl;
		exit(1);
	}


	std::vector<int> candidate_skill_vertices = copy_unordered_set_int_to_vector_int(skill_vertices);
	std::unordered_set<int> sampled_skill_vertices;

	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };

	while (sampled_skill_vertices.size() < sample_num) {
		boost::random::uniform_int_distribution<> dist{ 0, int(candidate_skill_vertices.size() - 1) };
		int ID = dist(gen);
		sampled_skill_vertices.insert(candidate_skill_vertices[ID]);
		candidate_skill_vertices.erase(candidate_skill_vertices.begin() + ID);
	}

	return sampled_skill_vertices;

}
#pragma endregion sample_random_skill_vertices

#pragma region
std::unordered_set<int> randomly_sample_vertex_groups_by_sizes(int sample_num,
	std::unordered_set<int>& candidate_vertex_groups, graph_hash_of_mixed_weighted& group_graph) {

	/*quantify possibility_ranges*/
	std::unordered_map<int, pair<int, int>> possibility_ranges_of_vertex_groups; // vertex_group, <left range, right range> 
	int range_step = 0; // range start from 0
	for (auto it = candidate_vertex_groups.begin(); it != candidate_vertex_groups.end(); it++) {
		int group_id = *it;
		int group_size = group_graph.degree(group_id);
		if (group_size > 0) {
			possibility_ranges_of_vertex_groups[group_id] = { range_step , range_step + group_size - 1 };
			range_step = range_step + group_size;
		}
	}

	/*randomly extract vertex groups by sizes*/
	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	std::unordered_set<int> sampled_vertex_groups;
	while (sampled_vertex_groups.size() < sample_num) {
		boost::random::uniform_int_distribution<> dist{ 0, range_step };
		int ID = dist(gen);
		for (auto it = possibility_ranges_of_vertex_groups.begin(); it != possibility_ranges_of_vertex_groups.end(); it++) {
			int group_id = it->first;
			int left_range = it->second.first;
			int right_range = it->second.second;
			if (ID >= left_range && ID <= right_range) {
				sampled_vertex_groups.insert(group_id);
				break;
			}
		}
	}

	return sampled_vertex_groups;

}
#pragma endregion randomly_sample_vertex_groups_by_sizes

#pragma region 
void read_Toronto_data(graph_hash_of_mixed_weighted& read_graph, graph_hash_of_mixed_weighted& read_group_graph,
	std::unordered_map<int, pair<double, double>>& read_intersection_geos,
	std::unordered_map<int, string>& read_facility_names) {

	/*this function can clear existing graph data*/
	read_graph.hash_of_vectors.clear();
	read_graph.hash_of_hashs.clear();
	read_group_graph.hash_of_vectors.clear();
	read_group_graph.hash_of_hashs.clear();
	read_intersection_geos.clear();
	read_facility_names.clear();

	int facility_ID_start = 1e6;

	std::unordered_map<std::string, int> INTERSECTION_IDs_unordered_map; // INTERSECTION_ID, ID
	std::unordered_map<std::string, int> TrafficCounts_unordered_map; // INTERSECTION_ID, TrafficCounts
	std::unordered_map<std::string, int> facility_unordered_map; // facility_names, ID
	std::unordered_map<std::string, std::vector<string>> INTERSECTION_ID_facility_unordered_map;

	int N, S;

	string file_name = "C:\\Users\\Yahui\\Google Drive\\Research\\My Paper\\Paper_group_Steiner_tree\\github\\toronto_vertices_car.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			if (count > 0) {

				std::vector<string> Parsed_content = parse_string(line_content, "_<and>_"); // parse line_content
				string INTERSECTION_ID = Parsed_content[0];
				int TrafficCounts = stoi(Parsed_content[1]);
				double lat = stod(Parsed_content[2]);
				double lon = stod(Parsed_content[3]);


				int v_ID = INTERSECTION_IDs_unordered_map.size();
				INTERSECTION_IDs_unordered_map[INTERSECTION_ID] = v_ID;
				TrafficCounts_unordered_map[INTERSECTION_ID] = TrafficCounts;
				read_intersection_geos[v_ID] = { lat , lon };


				for (int i = 4; i < Parsed_content.size(); i++) {
					string f_name = Parsed_content[i];
					if (facility_unordered_map.count(f_name) == 0) {
						int f_ID = facility_unordered_map.size() + facility_ID_start; // f_ID is unique
						facility_unordered_map[f_name] = f_ID;
					}
					INTERSECTION_ID_facility_unordered_map[INTERSECTION_ID].push_back(f_name);
				}
			}
			count++;
		}
		myfile.close(); //close the file


		for (auto it = INTERSECTION_IDs_unordered_map.begin(); it != INTERSECTION_IDs_unordered_map.end(); ++it) {
			string INTERSECTION_ID = it->first;
			int ID = it->second; // intersection id is unique
			graph_hash_of_mixed_weighted_add_vertex(read_graph, ID, TrafficCounts_unordered_map[INTERSECTION_ID]);  // nw = TrafficCounts
			graph_hash_of_mixed_weighted_add_vertex(read_group_graph, ID, 0);
		}
		for (auto it = facility_unordered_map.begin(); it != facility_unordered_map.end(); ++it) {
			string f_name = it->first;
			int ID = it->second; // f_ID is unique
			read_facility_names[ID] = f_name;
			graph_hash_of_mixed_weighted_add_vertex(read_group_graph, ID, 0);
		}


		for (auto it = INTERSECTION_ID_facility_unordered_map.begin(); it != INTERSECTION_ID_facility_unordered_map.end(); ++it) {
			string INTERSECTION_ID = it->first;
			std::vector<string> facilities = it->second;
			int v_ID = INTERSECTION_IDs_unordered_map[INTERSECTION_ID];

			for (int i = 0; i < facilities.size(); i++) {
				string f_name = facilities[i];
				int f_ID = facility_unordered_map[f_name];
				graph_hash_of_mixed_weighted_add_edge(read_group_graph, v_ID, f_ID, 1);
			}
		}
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}



	file_name = "C:\\Users\\Yahui\\Google Drive\\Research\\My Paper\\Paper_group_Steiner_tree\\github\\toronto_edges.txt";
	ifstream myfile2(file_name); // open the file
	if (myfile2.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile2, line_content)) // read file line by line
		{
			if (count > 0) {
				std::vector<string> Parsed_content = parse_string(line_content, "_<and>_");
				int v1 = INTERSECTION_IDs_unordered_map[Parsed_content[3]];
				int v2 = INTERSECTION_IDs_unordered_map[Parsed_content[4]];
				double dis = stod(Parsed_content[5]);
				graph_hash_of_mixed_weighted_add_edge(read_graph, v1, v2, dis); // ec = distance
			}
			count++;
		}
		myfile2.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

	cout << "INTERSECTION_IDs_unordered_map.size(): " << INTERSECTION_IDs_unordered_map.size() << endl;
	cout << "facility_unordered_map.size(): " << facility_unordered_map.size() << endl;

	cout << "num_vertices(read_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_graph) << endl;
	cout << "num_edges(read_graph): " << graph_hash_of_mixed_weighted_num_edges(read_graph) << endl;
	cout << "num_vertices(read_group_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_group_graph) << endl;
	cout << "num_edges(read_group_graph): " << graph_hash_of_mixed_weighted_num_edges(read_group_graph) << endl;

}
#pragma endregion read_Toronto_data 

#pragma region 
void read_dblp_v12_2498k(graph_hash_of_mixed_weighted& read_graph, graph_hash_of_mixed_weighted& read_group_graph, std::unordered_set<int>& group_vertices) {

	/*this function can clear existing graph data*/
	read_graph.hash_of_vectors.clear();
	read_graph.hash_of_hashs.clear();
	read_group_graph.hash_of_vectors.clear();
	read_group_graph.hash_of_hashs.clear();
	group_vertices.clear();

	int group_ID_start = 1e7;

	std::unordered_map<std::string, int> genres_ids;

	string file_name = "C:\\Users\\Yahui\\Google Drive\\Research\\My Paper\\Paper_group_Steiner_tree\\github\\dblp_v12_authors_2498k.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			if (count > 0) {
				std::vector<string> Parsed_content = parse_string(line_content, "<&>"); // parse line_content

				int author_id = stoi(Parsed_content[0]);
				double citation_num = stod(Parsed_content[3]);
				double paper_num = stod(Parsed_content[4]);
				graph_hash_of_mixed_weighted_add_vertex(read_graph, author_id, log(citation_num + 1)); // add vertex to read_graph; vertex weight
				graph_hash_of_mixed_weighted_add_vertex(read_group_graph, author_id, 0); // add vertex to read_group_graph

				std::vector<string> Parsed_fields = parse_string(Parsed_content[2], ","); // parse line_content
				for (int i = 0; i < Parsed_fields.size(); i++) {
					if (string_is_number(Parsed_fields[i])) {
						int group_id = group_ID_start + stoi(Parsed_fields[i]);
						group_vertices.insert(group_id);
						graph_hash_of_mixed_weighted_add_edge(read_group_graph, author_id, group_id, 0); // add edge to read_group_graph
					}
				}
			}
			count++;
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

	file_name = "C:\\Users\\Yahui\\Google Drive\\Research\\My Paper\\Paper_group_Steiner_tree\\github\\dblp_v12_linkes_2498k.txt";
	ifstream myfile2(file_name); // open the file
	if (myfile2.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile2, line_content)) // read file line by line
		{
			if (count > 0) {

				std::vector<string> Parsed_content = parse_string(line_content, "<&>"); // parse line_content

				int id1 = stoi(Parsed_content[0]);
				int id2 = stoi(Parsed_content[1]);

				graph_hash_of_mixed_weighted_add_edge(read_graph, id1, id2, 0); // add edge to read_graph

			}
			count++;
		}
		myfile2.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}


	cout << "num_vertices(read_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_graph) << endl;
	cout << "num_edges(read_graph): " << graph_hash_of_mixed_weighted_num_edges(read_graph) << endl;
	cout << "num_vertices(read_group_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_group_graph) << endl;
	cout << "num_edges(read_group_graph): " << graph_hash_of_mixed_weighted_num_edges(read_group_graph) << endl;

}
#pragma endregion read_dblp_v12_2498k

#pragma region 
void read_Movielens_25m(graph_hash_of_mixed_weighted& read_graph, graph_hash_of_mixed_weighted& read_group_graph,
	std::unordered_map<int, string>& movie_names, std::unordered_map<int, string>& genres_names) {

	/*this function can clear existing graph data*/
	read_graph.hash_of_vectors.clear();
	read_graph.hash_of_hashs.clear();
	read_group_graph.hash_of_vectors.clear();
	read_group_graph.hash_of_hashs.clear();
	movie_names.clear();
	genres_names.clear();

	int group_ID_start = 1e7;

	std::unordered_map<std::string, int> genres_ids;

	string file_name = "C:\\Users\\Yahui\\Google Drive\\Research\\My Paper\\Paper_group_Steiner_tree\\github\\MovieLens_25M_movie_info_35m_edges.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			if (count > 0) {

				std::vector<string> Parsed_content = parse_string(line_content, ":::"); // parse line_content

				//print_vector_string(Parsed_content);

				int movie_id = stoi(Parsed_content[0]);
				string movie_name = Parsed_content[1];
				movie_names[movie_id] = movie_name;

				//cout << movie_name << endl;

				double avg_star = stod(Parsed_content[2]);

				graph_hash_of_mixed_weighted_add_vertex(read_graph, movie_id, 5 - avg_star); // add vertex to read_graph; read_graph contains all movies; // the reverse of star, of the star of this movie is 3, then the node weight is 2
				graph_hash_of_mixed_weighted_add_vertex(read_group_graph, movie_id, 0); // add vertex to read_group_graph; read_group_graph contains all movies

				std::vector<string> genres = parse_string(Parsed_content[3], "|");
				for (int i = 0; i < genres.size(); i++) {
					if (genres_ids.count(genres[i]) == 0) {
						int genre_id = genres_ids.size() + group_ID_start;
						genres_names[genre_id] = genres[i];
						genres_ids[genres[i]] = genre_id;
					}
					int genre_id = genres_ids[genres[i]];
					graph_hash_of_mixed_weighted_add_edge(read_group_graph, movie_id, genre_id, 0); // add edge to read_group_graph
				}

			}
			count++;
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

	file_name = "C:\\Users\\Yahui\\Google Drive\\Research\\My Paper\\Paper_group_Steiner_tree\\github\\MovieLens_25M_movie_links_35m_edges.txt";
	ifstream myfile2(file_name); // open the file
	if (myfile2.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile2, line_content)) // read file line by line
		{
			if (count > 0) {

				std::vector<string> Parsed_content = parse_string(line_content, ":::"); // parse line_content

				int movie_id1 = stoi(Parsed_content[0]);
				int movie_id2 = stoi(Parsed_content[1]);
				int Number_of_common_5_star_raters = stoi(Parsed_content[2]);

				double ec = (double)1 / Number_of_common_5_star_raters; // how to define edge costs

				graph_hash_of_mixed_weighted_add_edge(read_graph, movie_id1, movie_id2, ec); // add edge to read_graph

			}
			count++;
		}
		myfile2.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}


	cout << "num_vertices(read_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_graph) << endl;
	cout << "num_edges(read_graph): " << graph_hash_of_mixed_weighted_num_edges(read_graph) << endl;
	cout << "num_vertices(read_group_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_group_graph) << endl;
	cout << "num_edges(read_group_graph): " << graph_hash_of_mixed_weighted_num_edges(read_group_graph) << endl;

}
#pragma endregion read_Movielens_25m 

#pragma region
void solve_VWGSTP_exp(string data_name, string save_name, int iteration_times, int V, int T, double lambda, double h,
	bool use_ENSteiner, bool use_IhlerA, bool use_exENSteiner, bool use_exIhlerA, bool use_FastAPP, bool use_fastAPP2, bool use_ImprovAPP,
	bool use_PartialOPT, bool use_DPBF, bool use_Basic, bool vertex_groups_sample_method) {

	/*output*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);
	outputFile << "V,T,lambda,h,g_min_size,cost_DPBF,time_DPBF,cost_ENSteiner,time_ENSteiner,cost_IhlerA,time_IhlerA,cost_exENSteiner,time_exENSteiner," <<
		"cost_exIhlerA,time_exIhlerA,cost_FastAPP,time_FastAPP,cost_fastAPP2,time_fastAPP2,cost_ImprovAPP,time_ImprovAPP,cost_PartialOPT,time_PartialOPT," <<
		"cost_exENSteinerP,time_exENSteinerP,cost_exIhlerAP,time_exIhlerAP,cost_FastAPPP,time_FastAPPP,cost_Basic,time_Basic" << endl;

	/*read raw dataset*/
	graph_hash_of_mixed_weighted read_graph, read_group_graph;
	if (data_name == "dblp_2498k") {
		std::unordered_set<int> group_vertices;
		read_dblp_v12_2498k(read_graph, read_group_graph, group_vertices);
		graph_hash_of_mixed_weighted_ec_update_pairwise_jaccard_distance(read_graph);
	}
	else if (data_name == "toronto") {
		std::unordered_map<int, pair<double, double>> read_intersection_geos;
		std::unordered_map<int, string> read_facility_names;
		read_Toronto_data(read_graph, read_group_graph, read_intersection_geos, read_facility_names); // node and edge weights are loaded here
	}
	else if (data_name == "movielens_25m") {
		std::unordered_map<int, string> movie_names, genres_names;
		read_Movielens_25m(read_graph, read_group_graph, movie_names, genres_names);
	}
	graph_hash_of_mixed_weighted_nw_ec_normalization(read_graph);



	/*find cpn and skill_vertices*/
	std::list<std::list<int>> cpn = graph_hash_of_mixed_weighted_connected_components(read_graph); 
	std::unordered_set<int> read_graph_skill_vertices; 
	for (auto it = read_graph.hash_of_vectors.begin(); it != read_graph.hash_of_vectors.end(); it++) {
		int v = it->first;
		auto search = read_group_graph.hash_of_hashs.find(v);
		if (search != read_group_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int skill_vertex = it2->first;
				read_graph_skill_vertices.insert(skill_vertex);
			}
		}
		else {
			auto search3 = read_group_graph.hash_of_vectors.find(v);
			for (auto it2 = search3->second.adj_vertices.begin(); it2 != search3->second.adj_vertices.end(); it2++) {
				int skill_vertex = it2->first;
				read_graph_skill_vertices.insert(skill_vertex);
			}
		}
	}


	//cout << "cpn.size():" << cpn.size() << endl;
	//std::list<int> max_cpn;
	//for (auto i = cpn.begin(); i != cpn.end(); i++) {
	//	if (max_cpn.size() < (*i).size()) {
	//		max_cpn = copy_list_int(*i);
	//	}
	//}
	//cout << "max_cpn.size(): " << max_cpn.size() << endl;


	/*iterations*/
	for (int times = 1; times <= iteration_times; times++) {

		cout << save_name << " iteration_times: " << times << " out of " << iteration_times << endl;

		/*randomly sample small graphs*/
		std::time_t now = std::time(0);
		boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
		boost::random::uniform_int_distribution<> dist{ 0, int(read_graph.hash_of_vectors.size() - 1) };


		std::unordered_set<int> sampled_skill_vertices;
		bool sampled_skill_vertices_is_feasible = false;


		if (V < read_graph.hash_of_vectors.size()) {
			unordered_set<int> selected_vertices = graph_hash_of_mixed_weighted_breadth_first_search_a_fixed_number_of_vertices_in_unconnected_graphs_start_from_maxcpn(read_graph, V);
			graph_hash_of_mixed_weighted small_read_graph = graph_hash_of_mixed_weighted_extract_subgraph_for_a_hash_of_vertices(read_graph, selected_vertices);

			/*compute small_read_graph_skill_vertices and sampled_skill_vertices*/
			std::unordered_set<int> small_read_graph_skill_vertices; // skill_vertices in small_read_graph
			for (auto it = small_read_graph.hash_of_vectors.begin(); it != small_read_graph.hash_of_vectors.end(); it++) {
				int v = it->first;
				auto search = read_group_graph.hash_of_hashs.find(v);
				if (search != read_group_graph.hash_of_hashs.end()) {
					for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
						int skill_vertex = it2->first;
						small_read_graph_skill_vertices.insert(skill_vertex);
					}
				}
				else {
					auto search3 = read_group_graph.hash_of_vectors.find(v);
					for (auto it2 = search3->second.adj_vertices.begin(); it2 != search3->second.adj_vertices.end(); it2++) {
						int skill_vertex = it2->first;
						small_read_graph_skill_vertices.insert(skill_vertex);
					}
				}
			}

			if (T > small_read_graph_skill_vertices.size()) {
				cout << "T > small_read_graph_skill_vertices.size()" << endl;
				times--;
				continue;
			}
			if (vertex_groups_sample_method == true) {
				sampled_skill_vertices = sample_random_skill_vertices(T, small_read_graph_skill_vertices); /*uniformly randomly sample vertex groups*/
			}
			else {
				sampled_skill_vertices = randomly_sample_vertex_groups_by_sizes(T, small_read_graph_skill_vertices, read_group_graph); /*randomly sample vertex groups by sizes*/
			}

			cpn = graph_hash_of_mixed_weighted_connected_components(small_read_graph); // small_read_graph is needed here
		}
		else {
			if (vertex_groups_sample_method == true) {
				sampled_skill_vertices = sample_random_skill_vertices(T, read_graph_skill_vertices); /*uniformly randomly sample vertex groups*/
			}
			else {
				sampled_skill_vertices = randomly_sample_vertex_groups_by_sizes(T, read_graph_skill_vertices, read_group_graph); /*randomly sample vertex groups by sizes*/
			}
		}


		/*solve instance in each maximal component*/
		double time_DPBF = 0, time_ENSteiner = 0, time_IhlerA = 0, time_exENSteiner = 0, time_exIhlerA = 0, time_FastAPP = 0, time_fastAPP2 = 0, 
			time_ImprovAPP = 0, time_PartialOPT = 0, time_exENSteinerP = 0, time_exIhlerAP = 0, time_FastAPPP = 0, time_Basic = 0;
		double final_cost_DPBF = INT_MAX, final_cost_ENSteiner = INT_MAX, final_cost_IhlerA = INT_MAX, 
			final_cost_exENSteiner = INT_MAX, final_cost_exIhlerA = INT_MAX, final_cost_FastAPP = INT_MAX, 
			final_cost_fastAPP2 = INT_MAX, final_cost_ImprovAPP = INT_MAX, final_cost_PartialOPT = INT_MAX, 
			final_cost_exENSteinerP = INT_MAX, final_cost_exIhlerAP = INT_MAX, final_cost_FastAPPP = INT_MAX, final_cost_Basic = INT_MAX;

		int g_min_size = 0; // this g_min is the sum of all g_mins in all components


		for (auto i = cpn.begin(); i != cpn.end(); i++) {

			graph_hash_of_mixed_weighted subgraph_g = graph_hash_of_mixed_weighted_extract_subgraph_for_a_list_of_vertices(read_graph, *i);
	
			bool this_subgraph_is_feasible;
			graph_hash_of_mixed_weighted subgraph_g_group_graph = produce_small_group_graph(sampled_skill_vertices, subgraph_g, read_group_graph, this_subgraph_is_feasible);

			int g_min = find_g_min(subgraph_g_group_graph, sampled_skill_vertices); // find g_min
			g_min_size = g_min_size + subgraph_g_group_graph.degree(g_min);
			//cout << "subgraph_g_group_graph.degree(g_min): " << subgraph_g_group_graph.degree(g_min) << endl;

			if (this_subgraph_is_feasible) {

				sampled_skill_vertices_is_feasible = true;

				if (use_ENSteiner) {
					auto begin = std::chrono::high_resolution_clock::now();
					graph_hash_of_mixed_weighted solu_ENSteiner = ENSteiner(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices);
					auto end = std::chrono::high_resolution_clock::now();
					double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_ENSteiner = time_ENSteiner + (double)runningtime;
					double cost_ENSteiner = graph_hash_of_mixed_weighted_lambda_cost(solu_ENSteiner, lambda);
					if (final_cost_ENSteiner > cost_ENSteiner) {
						final_cost_ENSteiner = cost_ENSteiner;
					}
				}

				if (use_IhlerA) {
					auto begin = std::chrono::high_resolution_clock::now();
					graph_hash_of_mixed_weighted solu_IhlerA = IhlerA(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices);
					auto end = std::chrono::high_resolution_clock::now();
					double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_IhlerA = time_IhlerA + (double)runningtime;
					double cost = graph_hash_of_mixed_weighted_lambda_cost(solu_IhlerA, lambda);
					if (final_cost_IhlerA > cost) {
						final_cost_IhlerA = cost;
					}
				}

				if (use_exENSteiner) {
					auto begin = std::chrono::high_resolution_clock::now();
					graph_hash_of_mixed_weighted solu_exENSteiner = exENSteiner(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices, lambda);
					auto end = std::chrono::high_resolution_clock::now();
					double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_exENSteiner = time_exENSteiner + (double)runningtime;
					double cost_exENSteiner = graph_hash_of_mixed_weighted_lambda_cost(solu_exENSteiner, lambda);
					if (final_cost_exENSteiner > cost_exENSteiner) {
						final_cost_exENSteiner = cost_exENSteiner;
					}

					begin = std::chrono::high_resolution_clock::now();
					remove_non_unique_group_leaves(solu_exENSteiner, subgraph_g_group_graph, sampled_skill_vertices, lambda);
					end = std::chrono::high_resolution_clock::now();
					runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_exENSteinerP = time_exENSteinerP + (double)runningtime;
					cost_exENSteiner = graph_hash_of_mixed_weighted_lambda_cost(solu_exENSteiner, lambda);
					if (final_cost_exENSteinerP > cost_exENSteiner) {
						final_cost_exENSteinerP = cost_exENSteiner;
					}
				}

				if (use_exIhlerA) {
					auto begin = std::chrono::high_resolution_clock::now();
					graph_hash_of_mixed_weighted solu_exIhlerA = exIhlerA(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices, lambda);
					auto end = std::chrono::high_resolution_clock::now();
					double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_exIhlerA = time_exIhlerA + (double)runningtime;
					double cost = graph_hash_of_mixed_weighted_lambda_cost(solu_exIhlerA, lambda);
					if (final_cost_exIhlerA > cost) {
						final_cost_exIhlerA = cost;
					}

					begin = std::chrono::high_resolution_clock::now();
					remove_non_unique_group_leaves(solu_exIhlerA, subgraph_g_group_graph, sampled_skill_vertices, lambda);
					end = std::chrono::high_resolution_clock::now();
					runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_exIhlerAP = time_exIhlerAP + (double)runningtime;
					cost = graph_hash_of_mixed_weighted_lambda_cost(solu_exIhlerA, lambda);
					if (final_cost_exIhlerAP > cost) {
						final_cost_exIhlerAP = cost;
					}
				}


				if (use_FastAPP) {
					auto begin = std::chrono::high_resolution_clock::now();
					graph_hash_of_mixed_weighted solu_fastAPP = FastAPP(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices, lambda);
					auto end = std::chrono::high_resolution_clock::now();
					double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_FastAPP = time_FastAPP + (double)runningtime;
					double cost = graph_hash_of_mixed_weighted_lambda_cost(solu_fastAPP, lambda);
					if (final_cost_FastAPP > cost) {
						final_cost_FastAPP = cost;
					}

					begin = std::chrono::high_resolution_clock::now();
					remove_non_unique_group_leaves(solu_fastAPP, subgraph_g_group_graph, sampled_skill_vertices, lambda);
					end = std::chrono::high_resolution_clock::now();
					runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_FastAPPP = time_FastAPPP + (double)runningtime;
					cost = graph_hash_of_mixed_weighted_lambda_cost(solu_fastAPP, lambda);
					if (final_cost_FastAPPP > cost) {
						final_cost_FastAPPP = cost;
					}
				}

				if (use_fastAPP2) {
					auto begin = std::chrono::high_resolution_clock::now();
					graph_hash_of_mixed_weighted solu_fastAPP = fastAPP2(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices, lambda);
					auto end = std::chrono::high_resolution_clock::now();
					double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_fastAPP2 = time_fastAPP2 + (double)runningtime;
					double cost = graph_hash_of_mixed_weighted_lambda_cost(solu_fastAPP, lambda);
					if (final_cost_fastAPP2 > cost) {
						final_cost_fastAPP2 = cost;
					}
				}

				if (use_ImprovAPP) {
					auto begin = std::chrono::high_resolution_clock::now();
					graph_hash_of_mixed_weighted solu = ImprovAPP(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices, lambda);
					auto end = std::chrono::high_resolution_clock::now();
					double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_ImprovAPP = time_ImprovAPP + (double)runningtime;
					double cost = graph_hash_of_mixed_weighted_lambda_cost(solu, lambda);
					if (final_cost_ImprovAPP > cost) {
						final_cost_ImprovAPP = cost;
					}
				}

				if (use_PartialOPT) {
					auto begin = std::chrono::high_resolution_clock::now();
					graph_hash_of_mixed_weighted solu_PartialOPT = PartialOPT(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices, lambda, h);
					auto end = std::chrono::high_resolution_clock::now();
					double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_PartialOPT = time_PartialOPT + (double)runningtime;
					double cost = graph_hash_of_mixed_weighted_lambda_cost(solu_PartialOPT, lambda);
					if (final_cost_PartialOPT > cost) {
						final_cost_PartialOPT = cost;
					}
				}


				
				if (use_DPBF) {
					auto begin = std::chrono::high_resolution_clock::now();
					graph_hash_of_mixed_weighted solu_DPBF = graph_hash_of_mixed_weighted_DPBF_vertex_edge_weighted(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices, lambda);
					auto end = std::chrono::high_resolution_clock::now();
					double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_DPBF = time_DPBF + (double)runningtime;
					double cost = graph_hash_of_mixed_weighted_lambda_cost(solu_DPBF, lambda);
					if (final_cost_DPBF > cost) {
						final_cost_DPBF = cost;
					}
				}

				if (use_Basic) {
					auto begin = std::chrono::high_resolution_clock::now();
					graph_hash_of_mixed_weighted solu_Basic = graph_hash_of_mixed_weighted_BasicProgressive_vertex_edge_weighted(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices, lambda);
					auto end = std::chrono::high_resolution_clock::now();
					double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
					time_Basic = time_Basic + (double)runningtime;
					double cost = graph_hash_of_mixed_weighted_lambda_cost(solu_Basic, lambda);
					if (final_cost_Basic > cost) {
						final_cost_Basic = cost;
					}
				}

			}
		}


		if (sampled_skill_vertices_is_feasible == true) { // there is a feasible solution
			outputFile << V << "," << T << "," << lambda << "," << h << "," << g_min_size << "," <<
				final_cost_DPBF << "," << time_DPBF << "," <<
				final_cost_ENSteiner << "," << time_ENSteiner << "," <<
				final_cost_IhlerA << "," << time_IhlerA << "," <<
				final_cost_exENSteiner << "," << time_exENSteiner << "," <<
				final_cost_exIhlerA << "," << time_exIhlerA << "," <<
				final_cost_FastAPP << "," << time_FastAPP << "," <<
				final_cost_fastAPP2 << "," << time_fastAPP2 << "," <<
				final_cost_ImprovAPP << "," << time_ImprovAPP << "," <<
				final_cost_PartialOPT << "," << time_PartialOPT << "," <<
				final_cost_exENSteinerP << "," << time_exENSteinerP << "," <<
				final_cost_exIhlerAP << "," << time_exIhlerAP << "," <<
				final_cost_FastAPPP << "," << time_FastAPPP << "," <<
				final_cost_Basic << "," << time_Basic << endl;
		}
		else {
			times--;
		}


	}

}
#pragma endregion solve_VWGSTP_exp

#pragma region
void solve_VWSTP_exp(string data_name, string save_name, int iteration_times, int V, int T, double lambda, bool vertex_groups_sample_method) {

	/*output*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);
	outputFile << "V,T,lambda,cost_LANCET,time_LANCET,cost_GKA,time_GKA" << endl;

	/*read raw dataset*/
	graph_hash_of_mixed_weighted read_graph, read_group_graph;
	if (data_name == "dblp_2498k") {
		std::unordered_set<int> group_vertices;
		read_dblp_v12_2498k(read_graph, read_group_graph, group_vertices);
		graph_hash_of_mixed_weighted_ec_update_pairwise_jaccard_distance(read_graph);
	}
	else if (data_name == "toronto") {
		std::unordered_map<int, pair<double, double>> read_intersection_geos;
		std::unordered_map<int, string> read_facility_names;
		read_Toronto_data(read_graph, read_group_graph, read_intersection_geos, read_facility_names); // node and edge weights are loaded here
	}
	else if (data_name == "movielens_25m") {
		std::unordered_map<int, string> movie_names, genres_names;
		read_Movielens_25m(read_graph, read_group_graph, movie_names, genres_names);
	}
	graph_hash_of_mixed_weighted_nw_ec_normalization(read_graph);



	/*find cpn and skill_vertices*/
	std::list<std::list<int>> cpn = graph_hash_of_mixed_weighted_connected_components(read_graph);
	std::unordered_set<int> read_graph_skill_vertices;
	for (auto it = read_graph.hash_of_vectors.begin(); it != read_graph.hash_of_vectors.end(); it++) {
		int v = it->first;
		auto search = read_group_graph.hash_of_hashs.find(v);
		if (search != read_group_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int skill_vertex = it2->first;
				read_graph_skill_vertices.insert(skill_vertex);
			}
		}
		else {
			auto search3 = read_group_graph.hash_of_vectors.find(v);
			for (auto it2 = search3->second.adj_vertices.begin(); it2 != search3->second.adj_vertices.end(); it2++) {
				int skill_vertex = it2->first;
				read_graph_skill_vertices.insert(skill_vertex);
			}
		}
	}


	/*iterations*/
	for (int times = 1; times <= iteration_times; times++) {

		cout << save_name << " iteration_times: " << times << " out of " << iteration_times << endl;

		/*randomly sample small graphs*/
		std::time_t now = std::time(0);
		boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
		boost::random::uniform_int_distribution<> dist{ 0, int(read_graph.hash_of_vectors.size() - 1) };


		std::unordered_set<int> sampled_skill_vertices;
		bool sampled_skill_vertices_is_feasible = false;


		if (V < read_graph.hash_of_vectors.size()) {
			unordered_set<int> selected_vertices = graph_hash_of_mixed_weighted_breadth_first_search_a_fixed_number_of_vertices_in_unconnected_graphs_start_from_maxcpn(read_graph, V);
			graph_hash_of_mixed_weighted small_read_graph = graph_hash_of_mixed_weighted_extract_subgraph_for_a_hash_of_vertices(read_graph, selected_vertices);

			/*compute small_read_graph_skill_vertices and sampled_skill_vertices*/
			std::unordered_set<int> small_read_graph_skill_vertices; // skill_vertices in small_read_graph
			for (auto it = small_read_graph.hash_of_vectors.begin(); it != small_read_graph.hash_of_vectors.end(); it++) {
				int v = it->first;
				auto search = read_group_graph.hash_of_hashs.find(v);
				if (search != read_group_graph.hash_of_hashs.end()) {
					for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
						int skill_vertex = it2->first;
						small_read_graph_skill_vertices.insert(skill_vertex);
					}
				}
				else {
					auto search3 = read_group_graph.hash_of_vectors.find(v);
					for (auto it2 = search3->second.adj_vertices.begin(); it2 != search3->second.adj_vertices.end(); it2++) {
						int skill_vertex = it2->first;
						small_read_graph_skill_vertices.insert(skill_vertex);
					}
				}
			}

			if (T > small_read_graph_skill_vertices.size()) {
				cout << "T > small_read_graph_skill_vertices.size()" << endl;
				times--;
				continue;
			}
			if (vertex_groups_sample_method == true) {
				sampled_skill_vertices = sample_random_skill_vertices(T, small_read_graph_skill_vertices); /*uniformly randomly sample vertex groups*/
			}
			else {
				sampled_skill_vertices = randomly_sample_vertex_groups_by_sizes(T, small_read_graph_skill_vertices, read_group_graph); /*randomly sample vertex groups by sizes*/
			}

			cpn = graph_hash_of_mixed_weighted_connected_components(small_read_graph); // small_read_graph is needed here
		}
		else {
			if (vertex_groups_sample_method == true) {
				sampled_skill_vertices = sample_random_skill_vertices(T, read_graph_skill_vertices); /*uniformly randomly sample vertex groups*/
			}
			else {
				sampled_skill_vertices = randomly_sample_vertex_groups_by_sizes(T, read_graph_skill_vertices, read_group_graph); /*randomly sample vertex groups by sizes*/
			}
		}


		/*solve instance in each maximal component*/
		double time_GKA = 0, time_LANCET = 0;
		double final_cost_GKA = INT_MAX, final_cost_LANCET = INT_MAX;

		int g_min_size = 0; // this g_min is the sum of all g_mins in all components


		for (auto i = cpn.begin(); i != cpn.end(); i++) {

			graph_hash_of_mixed_weighted subgraph_g = graph_hash_of_mixed_weighted_extract_subgraph_for_a_list_of_vertices(read_graph, *i);

			bool this_subgraph_is_feasible;
			graph_hash_of_mixed_weighted subgraph_g_group_graph = produce_small_group_graph(sampled_skill_vertices, subgraph_g, read_group_graph, this_subgraph_is_feasible);

			int g_min = find_g_min(subgraph_g_group_graph, sampled_skill_vertices); // find g_min
			g_min_size = g_min_size + subgraph_g_group_graph.degree(g_min);
			//cout << "subgraph_g_group_graph.degree(g_min): " << subgraph_g_group_graph.degree(g_min) << endl;

			if (this_subgraph_is_feasible) {

				sampled_skill_vertices_is_feasible = true;

				/*transformation_to_NWSTP*/
				/*time complexity: O(|V|+|E|)*/
				graph_hash_of_mixed_weighted G_t;
				transformation_to_NWSTP(subgraph_g, subgraph_g_group_graph, sampled_skill_vertices, lambda, G_t);

				/*time complexity: O(|V|+|E|)*/
				graph_hash_of_mixed_weighted G2 = generate_G2(G_t); // both node weights and lambda have been embeded into edge costs in G2

				auto begin1 = std::chrono::high_resolution_clock::now();
				graph_hash_of_mixed_weighted theta_GKA = Guha_16103_algorithm(G_t, sampled_skill_vertices, G2);
				auto end1 = std::chrono::high_resolution_clock::now();
				double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
				time_GKA = time_GKA + runningtime1;
				for (auto it = sampled_skill_vertices.begin(); it != sampled_skill_vertices.end(); it++) {
					graph_hash_of_mixed_weighted_remove_vertex(theta_GKA, *it); // remove M, otherwise M changes with V
				}
				double cost_GKA = graph_hash_of_mixed_weighted_sum_of_nw_ec(theta_GKA);
				if (final_cost_GKA > cost_GKA) {
					final_cost_GKA = cost_GKA;
				}

				/*time complexity: O(|V|+|E|)*/
				update_G2_ec(G_t); // both node weights and lambda have been embeded into edge costs 

				auto begin2 = std::chrono::high_resolution_clock::now();
				graph_hash_of_mixed_weighted theta_LANCET = LANCET(G_t, sampled_skill_vertices);
				auto end2 = std::chrono::high_resolution_clock::now();
				double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
				time_LANCET = time_LANCET + runningtime2;
				for (auto it = sampled_skill_vertices.begin(); it != sampled_skill_vertices.end(); it++) {
					graph_hash_of_mixed_weighted_remove_vertex(theta_LANCET, *it);
				}
				double cost_LANCET = graph_hash_of_mixed_weighted_sum_of_nw_ec(theta_LANCET);
				if (final_cost_LANCET > cost_LANCET) {
					final_cost_LANCET = cost_LANCET;
				}

			}
		}


		if (sampled_skill_vertices_is_feasible == true) { // there is a feasible solution
			outputFile << V << "," << T << "," << lambda << "," <<
				final_cost_LANCET << "," << time_LANCET << "," <<
				final_cost_GKA << "," << time_GKA << endl;
		}
		else {
			times--;
		}


	}

}
#pragma endregion solve_VWSTP_exp

#pragma region
void solve_VWGSTP_toronto_experiments() {

	int iteration_times = 100;
	int V = 46073;
	int h = 3;
	int T = 8;
	double lambda = 0.33;

	bool use_ENSteiner, use_IhlerA;

	if (1) {
		/*uniform V*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false;
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_uniform_V_1.csv", iteration_times, 25073, T, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, true);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_uniform_V_2.csv", iteration_times, 32073, T, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, true);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_uniform_V_3.csv", iteration_times, 39073, T, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, true);
			use_ENSteiner = true, use_IhlerA = true;
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_uniform_V_4.csv", iteration_times, V, T, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, true);
		}

		/*uniform T*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false;
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_uniform_T_1.csv", iteration_times, V, 6, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, true);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_uniform_T_2.csv", iteration_times, V, 7, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, true);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_uniform_T_3.csv", iteration_times, V, 9, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, true);
		}

		/*uniform lambda*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false;
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_uniform_lambda_1.csv", iteration_times, V, T, 0, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, true);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_uniform_lambda_2.csv", iteration_times, V, T, 0.67, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, true);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_uniform_lambda_3.csv", iteration_times, V, T, 1, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, true);
		}
	}

	
	if (1) {
		use_ENSteiner = false, use_IhlerA = false;
		/*size V*/
		if (1) {
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_size_V_1.csv", iteration_times, 25073, T, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, false);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_size_V_2.csv", iteration_times, 32073, T, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, false);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_size_V_3.csv", iteration_times, 39073, T, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, false);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_size_V_4.csv", iteration_times, V, T, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, false);
		}

		/*size T*/
		if (1) {
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_size_T_1.csv", iteration_times, V, 6, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, false);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_size_T_2.csv", iteration_times, V, 7, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, false);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_size_T_3.csv", iteration_times, V, 9, lambda, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, false);
		}

		/*size lambda*/
		if (1) {
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_size_lambda_1.csv", iteration_times, V, T, 0, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, false);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_size_lambda_2.csv", iteration_times, V, T, 0.67, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, false);
			solve_VWGSTP_exp("toronto", "EXP_solve_VWGSTP_toronto_size_lambda_3.csv", iteration_times, V, T, 1, h, use_ENSteiner, use_IhlerA, true, true, true, 0, true, true, true, 0, false);
		}
	}

}
#pragma endregion solve_VWGSTP_toronto_experiments

#pragma region
void solve_VWGSTP_movielens_experiments() {

	int iteration_times = 100;
	int V = 62423;
	int h = 3;
	int T = 5;
	double lambda = 0.33;


	bool use_ENSteiner, use_IhlerA, use_exIhlerA, use_PartialOPT, use_DPBF;

	if (0) {
		/*uniform V*/
		if (0) {
			use_ENSteiner = true, use_IhlerA = true, use_exIhlerA = true, use_PartialOPT = true, use_DPBF = true;
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_V_1.csv", iteration_times, 2423, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_V_onlyexIhlerA.csv", iteration_times, 5423, T, lambda, h, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, true);
			use_ENSteiner = false, use_IhlerA = false; use_exIhlerA = false; use_PartialOPT = false, use_DPBF = true;
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_V_2.csv", iteration_times, 22423, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_V_3.csv", iteration_times, 42423, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_V_4.csv", iteration_times, V, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
		}

		/*uniform T*/
		if (0) {
			use_ENSteiner = false, use_IhlerA = false; use_exIhlerA = false; use_PartialOPT = false, use_DPBF = true;
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_T_1.csv", iteration_times, V, 4, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_T_2.csv", iteration_times, V, 6, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			use_DPBF = false;
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_T_3.csv", iteration_times, V, 7, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
		}

		/*uniform lambda*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false; use_exIhlerA = false; use_PartialOPT = false, use_DPBF = true;
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_lambda_1.csv", iteration_times, V, T, 0, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_lambda_2.csv", iteration_times, V, T, 0.67, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_uniform_lambda_3.csv", iteration_times, V, T, 1, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
		}
	}


	if (1) {
		/*size V*/
		if (0) {
			use_ENSteiner = false, use_IhlerA = false, use_exIhlerA = true, use_PartialOPT = true, use_DPBF = true;
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_V_1.csv", iteration_times, 2000, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_V_onlyexIhlerA.csv", iteration_times, 5423, T, lambda, h, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, false);
			use_exIhlerA = false; use_PartialOPT = false, use_DPBF = true;
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_V_2.csv", iteration_times, 22423, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_V_3.csv", iteration_times, 42423, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_V_4.csv", iteration_times, V, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
		}

		/*size T*/
		if (0) {
			use_ENSteiner = false, use_IhlerA = false; use_exIhlerA = false; use_PartialOPT = false, use_DPBF = true;
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_T_1.csv", iteration_times, V, 4, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_T_2.csv", iteration_times, V, 6, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			use_DPBF = false;
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_T_3.csv", iteration_times, V, 7, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
		}

		/*size lambda*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false; use_exIhlerA = false; use_PartialOPT = false, use_DPBF = true;
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_lambda_1.csv", iteration_times, V, T, 0, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_lambda_2.csv", iteration_times, V, T, 0.67, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("movielens_25m", "EXP_solve_VWGSTP_movielens_size_lambda_3.csv", iteration_times, V, T, 1, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
		}
	}

}
#pragma endregion solve_VWGSTP_movielens_experiments

#pragma region
void solve_VWGSTP_dblp_2498k_experiments() {


	int iteration_times = 100;
	int V = 2497782;
	int h = 3;
	int T = 6;
	double lambda = 0.33;

	bool use_ENSteiner, use_IhlerA, use_exIhlerA, use_PartialOPT, use_DPBF;

	/*uniform*/
	if (0) {
		/*Vary_V*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false, use_exIhlerA = true, use_PartialOPT = true, use_DPBF = true;
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_uniform_Vary_V_1.csv", iteration_times, 297782, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			use_DPBF = false, use_PartialOPT = false;
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_uniform_Vary_V_2.csv", iteration_times, 1097782, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_uniform_Vary_V_3.csv", iteration_times, 1797782, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			use_ENSteiner = true, use_IhlerA = true;
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_uniform_Vary_V_4.csv", iteration_times, V, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
		}


		/*Vary_T*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false, use_exIhlerA = true, use_PartialOPT = false, use_DPBF = false;
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_uniform_Vary_T_1.csv", iteration_times, V, 5, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_uniform_Vary_T_2.csv", iteration_times, V, 7, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_uniform_Vary_T_3.csv", iteration_times, V, 8, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
		}


		/*Vary_lambda*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false, use_exIhlerA = true, use_PartialOPT = false, use_DPBF = false;
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_uniform_Vary_lambda_1.csv", iteration_times, V, T, 0, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_uniform_Vary_lambda_2.csv", iteration_times, V, T, 0.67, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_uniform_Vary_lambda_3.csv", iteration_times, V, T, 1, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, true);
		}
	}

	
	/*size*/
	if (1) {
		/*Vary_V*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false, use_exIhlerA = true, use_PartialOPT = true, use_DPBF = true;
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_V_1.csv", iteration_times, 37782, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			use_PartialOPT = false;
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_V_onlyexIhlerA.csv", iteration_times, 197782, T, lambda, h, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, false);
			use_exIhlerA = false;
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_V_2.csv", iteration_times, 1097782, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_V_3.csv", iteration_times, 1797782, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_V_4.csv", iteration_times, V, T, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
		}

		/*Vary_T*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false, use_exIhlerA = false, use_PartialOPT = false, use_DPBF = true;
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_T_1.csv", iteration_times, V, 3, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_T_2.csv", iteration_times, V, 4, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_T_3.csv", iteration_times, V, 5, lambda, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
		}


		/*Vary_lambda*/
		if (1) {
			use_ENSteiner = false, use_IhlerA = false, use_exIhlerA = false, use_PartialOPT = false, use_DPBF = true;
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_lambda_1.csv", iteration_times, V, T, 0, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_lambda_2.csv", iteration_times, V, T, 0.67, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
			solve_VWGSTP_exp("dblp_2498k", "EXP_solve_VWGSTP_dblp_2498k_size_Vary_lambda_3.csv", iteration_times, V, T, 1, h, use_ENSteiner, use_IhlerA, true, use_exIhlerA, true, 0, true, use_PartialOPT, use_DPBF, 0, false);
		}
	}


}
#pragma endregion solve_VWGSTP_dblp_2498k_experiments

#pragma region
void compare_DPBF_Basic() {

	int iteration_times = 100;
	double lambda = 0.33;

	/*uniform*/
	if (0) {
		/*Toronto*/
		if (0) {
			int T = 5;
			solve_VWGSTP_exp("toronto", "EXP_compare_DPBF_Basic_toronto.csv", iteration_times, 46073, T, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, true);
		}

		/*DBLP*/
		if (0) {
			int T = 5;
			solve_VWGSTP_exp("dblp_2498k", "EXP_compare_DPBF_Basic_dblp.csv", iteration_times, 107782, T, lambda, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, true);
		}

		/*MovieLens*/
		if (1) {
			int T = 5;
			solve_VWGSTP_exp("movielens_25m", "EXP_compare_DPBF_Basic_movie.csv", iteration_times, 10423, T, lambda, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, true);
		}
	}

	

	/*size*/
	if (1) {
		/*Toronto*/
		if (1) {
			int T = 5;
			solve_VWGSTP_exp("toronto", "EXP_compare_DPBF_Basic_toronto_size.csv", iteration_times, 46073, T, lambda, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0);
		}

		/*DBLP*/
		if (1) {
			int T = 5;
			solve_VWGSTP_exp("dblp_2498k", "EXP_compare_DPBF_Basic_dblp_size.csv", iteration_times, 107782, T, lambda, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0);
		}

		/*MovieLens*/
		if (1) {
			int T = 5;
			solve_VWGSTP_exp("movielens_25m", "EXP_compare_DPBF_Basic_movie_size.csv", iteration_times, 10423, T, lambda, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0);
		}
	}







}
#pragma endregion compare_DPBF_Basic

#pragma region
void vary_h() {

	int iteration_times = 100;

	if (1) {
		int T = 6;
		double lambda = 0.33;
		solve_VWGSTP_exp("toronto", "EXP_toronto_uniform_vary_h_1.csv", iteration_times, 46073, T, lambda, 3, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, true);
		solve_VWGSTP_exp("toronto", "EXP_toronto_uniform_vary_h_2.csv", iteration_times, 46073, T, lambda, 4, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, true);
		solve_VWGSTP_exp("toronto", "EXP_toronto_uniform_vary_h_3.csv", iteration_times, 46073, T, lambda, 5, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, true);
		solve_VWGSTP_exp("toronto", "EXP_toronto_uniform_vary_h_4.csv", iteration_times, 46073, T, lambda, 6, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, true);
	}


}
#pragma endregion vary_h

#pragma region
void solve_VWSTP() {

	int iteration_times = 100;

	if (1) {
		int T = 6;
		double lambda = 0.33;
		solve_VWSTP_exp("toronto", "EXP_toronto_uniform_solve_VWSTP_1.csv", iteration_times, 1000, T, lambda, true);
		solve_VWSTP_exp("toronto", "EXP_toronto_uniform_solve_VWSTP_2.csv", iteration_times, 2000, T, lambda, true);
		solve_VWSTP_exp("toronto", "EXP_toronto_uniform_solve_VWSTP_3.csv", iteration_times, 3000, T, lambda, true);
		solve_VWSTP_exp("toronto", "EXP_toronto_uniform_solve_VWSTP_4.csv", iteration_times, 4000, T, lambda, true);
	}


}
#pragma endregion solve_VWSTP





int main()
{
	srand(time(NULL)); //  seed random number generator   

	auto begin = std::chrono::high_resolution_clock::now();

	/*the two values below are for #include <graph_hash_of_mixed_weighted.h>*/
	graph_hash_of_mixed_weighted_turn_on_value = 1e3;
	graph_hash_of_mixed_weighted_turn_off_value = 1e1;

	solve_VWGSTP_toronto_experiments();


	auto end = std::chrono::high_resolution_clock::now();
	double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s


	cout << "END    runningtime: " << runningtime << "s" << endl;

	getchar();

}



