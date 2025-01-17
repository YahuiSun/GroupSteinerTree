# Finding Group Steiner Trees in Graphs with both Vertex and Edge Weights

These files are for the following publication:

Yahui Sun, Xiaokui Xiao, Bin Cui, Saman Halgamuge, Theodoros Lappas, and Jun Luo. "Finding group Steiner trees in graphs with both vertex and edge weights", Proceedings of the VLDB Endowment (2021) 

The introduction of these files are as follows. For any enquiry, please feel free to contact Yahui SUN: yahuisun@outlook.com


# Datasets

There are three datasets: Toronto, DBLP and MovieLens. 

Two files can be extracted from "toronto.zip" (There are 46,073 vertices, 68,353 edges, and 35 types of facilities in total):
1) "toronto_vertices_car.txt": The items in each line are: INTERSECTION_ID\_\<and\>\_TrafficCounts\_\<and\>\_lat\_\<and\>\_lon\_\<and\>\_facilities, such as "13455668\_\<and\>\_2978\_\<and\>\_43.717172239\_\<and\>\_-79.5255278\_\<and\>\_Park\_\<and\>\_OUTDOORS Public art work", which means that road intersection "13455668" has a traffic count "2978" and a location "43.717172239,-79.5255278", and has two types of facilities nearby "Park" and "OUTDOORS Public art work".
2) "toronto_edges.txt": The items in each line are: CENTRELINE_ID\_\<and\>\_LINEAR_NAME_ID(Street Name ID)\_\<and\>\_LINEAR_NAME_FULL(Full street name)\_\<and\>\_FROM_INTERSECTION_ID\_\<and\>\_TO_INTERSECTION_ID\_\<and\>\_DISTANCE, such as "30079678\_\<and\>\_ 19155\_\<and\>\_Waterfront Trl\_\<and\>\_30079676\_\<and\>\_30079656\_\<and\>\_0.407088173808", which means that CENTRELINE_ID "30079678" corresponds to Street Name ID "19155", and has a name "Waterfront Trl", and is between two road intersection IDs "30079676" and "30079656", and has a distance of "0.407088173808" km.

Three files can be extracted from "dblp_v12.zip" (There are 2,497,782 vertices, 12,786,329 edges, and 127,726 research topics in total.):
1) "dblp_v12_fields_2498k.txt": The items in each line are: Fields_of_study_ID\<\&\>Fields_of_study_name, such as "28341\<\&\>Biological immune system", which means that the field of study (research topic) "Biological immune system" has an ID of 28341.
2) "dblp_v12_authors_2498k.txt": The items in each line are: Author_ID\<\&\>Author_name\<\&\>Fields_of_study_IDs\<\&\>Citation_num\<\&\>Paper_num, such as "59\<\&\>Ryo Muramatsu\<\&\>616,5,7,617,619,201,530,620\<\&\>1\<\&\>1", which means that Author 59 has a name Ryo Muramatsu, and conducts researches in the fileds of "616,5,7,617,619,201,530,620", and has 1 citation and 1 paper.
3) "dblp_v12_linkes_2498k.txt": The items in each line are: Author_ID1\<\&\>Author_ID2, such as "1879\<\&\>58716", which means that author 1879 has co-authored publications with author 58716.

Two files can be extracted from "MovieLens_25M.zip" (There are 62,423 vertices, 35,323,774 edges, and 19 genres in total.):
1) "MovieLens_25M_movie_info_35m_edges.txt": The items in each line are: Movie_ID(start from 0):::Movie_name:::Average_star:::genres, such as "399:::Homage (1995):::2.536:::Drama", which means that Movie 399 has a name of Homage (1995), and has an average rating star of 2.536, and is about Drama.
2) "MovieLens_25M_movie_links_35m_edges.txt": The items in each line are: Movie_ID1(start from 0):::Movie_ID2(start from 0):::Number_of_common_5_star_raters, such as "1252:::1395:::79", which means that there are persons who rate five stars to both Movies 1252 and 1395, and the number of such persons is 79.


<b>We use codes in the "read_Toronto_data", "read_dblp_v12_2498k" and "read_Movielens_25m" regions in the following "GST.cpp" to load these datasets.</b>


# C++ codes 

The C++ source codes are in <b>GST.cpp</b>. 

<b>It is recommended to fold all the regions of codes for easy reading</b> (by pressing Ctrl+M+O in VisualStudio). 

Running these codes requires some header files from my own YS-Graph-Library: https://github.com/YahuiSun/YS-Graph-Library (see ysgraph_2021****.zip), and two header files (random.hpp and fibonacci_heap.hpp) from the Boost library: https://www.boost.org/ 

After making the header files ready, all the experiment results in our paper can be produced by runnning the codes below "/\*experiments\*/", i.e., you can run:

int main()
{
	srand(time(NULL)); //  seed random number generator   

	auto begin = std::chrono::high_resolution_clock::now();

	/*the two values below are for #include <graph_hash_of_mixed_weighted.h>*/
	graph_hash_of_mixed_weighted_turn_on_value = 1e3;
	graph_hash_of_mixed_weighted_turn_off_value = 1e1;

	parallel_experiments();


	auto end = std::chrono::high_resolution_clock::now();
	double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s


	cout << "END    runningtime: " << runningtime << "s" << endl;

}

The experiment results will be saved in csv files.

To read these C++ codes in detail, it is recommended to start from the codes below "/\*experiments\*/". More detailed codes in other regions can then be traced. Again, for any enquiry, please feel free to contact Yahui SUN: yahuisun@outlook.com





