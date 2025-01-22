import re

def fix_dot_file(input_file, output_file):
    with open(input_file, "r") as infile:
        content = infile.read()

    # Wrap negative and positive node IDs in quotes in node definitions
    content = re.sub(r"(?<=\n)(-?\d+)\s*\[", r'"\1" [', content)

    # Wrap source and destination IDs in quotes for edge definitions
    content = re.sub(r"(?<=\n)(-?\d+)\s*->\s*(-?\d+)", r'"\1" -> "\2"', content)

    # Write the fixed content to a new .dot file
    with open(output_file, "w") as outfile:
        outfile.write(content)

    print(f"Fixed .dot file written to {output_file}")
    
# Input and output file paths
input_dot_file = "build/output.dot"
output_dot_file = "build/fixed_output.dot"

fix_dot_file(input_dot_file, output_dot_file)