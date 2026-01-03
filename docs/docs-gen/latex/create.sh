#!/bin/bash
set -euo pipefail

# Validate input arguments
if [[ $# -lt 2 ]]; then
    echo "Error: Missing required arguments" >&2
    echo "Usage: $0 <output_directory> <document_name>" >&2
    exit 1
fi

output_dir="$1"
doc_name="$2"

# Check if output directory already exists
if [[ -e "$output_dir" ]]; then
    echo "Error: Output directory '$output_dir' already exists" >&2
    exit 1
fi

# Create directory structure
mkdir -p "$output_dir"/{00-DocumentSettings,01-FrontMatter,02-Body,03-EndMatter}

# Find the git root from the current script location
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if ! gitroot=$(cd "$script_dir" && git rev-parse --show-toplevel 2>/dev/null); then
    echo "Error: Script is not in a git repository" >&2
    exit 1
fi

gitrootToSnippet="${gitroot}/docs/docs-gen/latex/snippet"

# Verify snippet directory exists
if [[ ! -d "$gitrootToSnippet" ]]; then
    echo "Error: Snippet directory not found at $gitrootToSnippet" >&2
    exit 1
fi

echo "Using snippet directory: $gitrootToSnippet"
tree .

# Define file mappings (source -> destination)
declare -A file_map=(
    ["Latex.tex"]="${output_dir}/${doc_name}.tex"
    ["Preamble.tex"]="${output_dir}/00-DocumentSettings/Preamble.tex"
    ["PreTitle.tex"]="${output_dir}/00-DocumentSettings/PreTitle.tex"
    ["Definitions.tex"]="${output_dir}/00-DocumentSettings/Definitions.tex"
    ["Abstract.tex"]="${output_dir}/01-FrontMatter/Abstract.tex"
    ["Title.tex"]="${output_dir}/01-FrontMatter/Title.tex"
    ["TOC.tex"]="${output_dir}/01-FrontMatter/TOC.tex"
    ["FrontMatter.tex"]="${output_dir}/01-FrontMatter/FrontMatter.tex"
    ["Body.tex"]="${output_dir}/02-Body/Body.tex"
    ["EndMatter.tex"]="${output_dir}/03-EndMatter/EndMatter.tex"
    ["References.tex"]="${output_dir}/03-EndMatter/References.tex"
    ["References.bib"]="${output_dir}/03-EndMatter/References.bib"
)

# Copy files with error checking
for src_file in "${!file_map[@]}"; do
    src_path="${gitrootToSnippet}/${src_file}"
    dst_path="${file_map[$src_file]}"
    
    if [[ ! -f "$src_path" ]]; then
        echo "Error: Source file not found: $src_path" >&2
        exit 1
    fi
    
    cp "$src_path" "$dst_path"
done

echo "LaTeX project created successfully at $output_dir"
