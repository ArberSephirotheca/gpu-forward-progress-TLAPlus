import re
import pydot

# Function to format labels
def format_label(label):
    if not label:
        return ""
    # Replace escaped newlines with actual newlines
    label = label.replace("\\n", "\n")
    # Replace escaped quotes with normal quotes
    label = label.replace('\\"', '"')
    # Add proper indentation for better readability
    lines = label.split("\n")
    formatted_lines = []
    indent = 0
    for line in lines:
        if ">>" in line or "]" in line:
            indent -= 1
        formatted_lines.append("    " * max(indent, 0) + line.strip())
        if "<<" in line or "[" in line:
            indent += 1
    return "\n".join(formatted_lines)

# Main function to extract a path and reformat labels
def extract_path(dot_file, start_node, end_node, output_file):
    # Load the DOT file
    graphs = pydot.graph_from_dot_file(dot_file)
    if not graphs or len(graphs) == 0:
        print("Error: Unable to parse the DOT file. Check its syntax.")
        return

    graph = graphs[0]  # Assuming only one graph in the file

    # Create mappings for adjacency and labels
    adjacency_list = {}
    edge_labels = {}
    node_labels = {}

    # Extract all nodes and their labels
    for node in graph.get_nodes():
        node_id = node.get_name().strip('"')
        label = node.get_label()
        if label:
            node_labels[node_id] = format_label(label.strip('"'))

    # Extract all edges and their labels
    for edge in graph.get_edges():
        src = edge.get_source().strip('"')
        dst = edge.get_destination().strip('"')
        if src not in adjacency_list:
            adjacency_list[src] = []
        adjacency_list[src].append(dst)
        label = edge.get_label()
        if label:
            edge_labels[(src, dst)] = format_label(label.strip('"'))

    # DFS to find the path
    def dfs(current, target, visited, path):
        if current in visited:
            return None
        if current == target:
            return path + [current]
        visited.add(current)
        for neighbor in adjacency_list.get(current, []):
            result = dfs(neighbor, target, visited, path + [current])
            if result:
                return result
        visited.remove(current)
        return None

    # Extract the path
    visited = set()
    path = dfs(start_node, end_node, visited, [])

    if not path:
        print("No path found.")
        return

    print("Path found:", " -> ".join(path))

    # Write the subgraph manually to preserve and format labels
    with open(output_file, "w") as outfile:
        outfile.write("digraph G {\n")
        
        # Write nodes with formatted labels
        for node in path:
            label = node_labels.get(node, "")
            outfile.write(f'    "{node}" [label="{label}"];\n')

        # Write edges with formatted labels
        for i in range(len(path) - 1):
            src, dst = path[i], path[i + 1]
            label = edge_labels.get((src, dst), "")
            outfile.write(f'    "{src}" -> "{dst}" [label="{label}"];\n')

        outfile.write("}\n")

    print(f"Path with formatted labels written to {output_file}")

# Input your DOT file and nodes
dot_file = "build/fixed_output.dot"
start_node = "5132644038964620299"  # Replace with your start node
end_node = "-836133892222178721"      # Replace with your end node
output_file = "path_subgraph.dot"

# Extract the path and write to a file
extract_path(dot_file, start_node, end_node, output_file)