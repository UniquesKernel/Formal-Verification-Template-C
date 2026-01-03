#!/bin/bash

# Lean Project Setup Script
# This script sets up a new Lean project with the given name

set -e

# Install Lean 4 if not already installed
echo "Checking for Lean 4 installation..."
if ! command -v lean &> /dev/null; then
    echo "Lean 4 not found. Installing Lean 4 using elan..."
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
    
    # Source the elan environment to make lean available in this script
    source $HOME/.elan/env
    
    echo "✓ Lean 4 installed successfully!"
else
    echo "✓ Lean 4 is already installed"
fi

echo ""

# Check if project name is provided
if [ $# -eq 0 ]; then
    echo "Usage: ./create_lean_project.sh <project-name> [root-folder]"
    echo ""
    echo "Arguments:"
    echo "  <project-name>   Name of the Lean project to create (required)"
    echo "  [root-folder]    Root folder for projects (optional, defaults to 'lean')"
    echo ""
    echo "Examples:"
    echo "  ./create_lean_project.sh my_project"
    echo "  ./create_lean_project.sh my_project lean_projects"
    exit 1
fi

PROJECT_NAME="$1"
ROOT_FOLDER="${2:-lean}"  # Default to "lean" if not provided
PROJECT_DIR="${ROOT_FOLDER}"

# Check if project directory already exists
if [ -d "$PROJECT_DIR" ]; then
    echo "Error: Directory '$PROJECT_DIR' already exists"
    exit 1
fi

# Create root directory if it doesn't exist
mkdir -p "$ROOT_FOLDER"

# Function to convert project name to PascalCase module name
# Example: my-project -> MyProject, test_project -> TestProject
to_pascal_case() {
    local name="$1"
    # Replace hyphens and underscores with spaces, capitalize each word, remove spaces
    echo "$name" | sed 's/[-_]/ /g' | awk '{for(i=1;i<=NF;i++) $i=toupper(substr($i,1,1))substr($i,2)} 1' | tr -d ' '
}

# Convert project name to module name
MODULE_NAME=$(to_pascal_case "$PROJECT_NAME")

# Initialize project using lake
echo "Initializing Lean project '$PROJECT_NAME' using lake..."
mkdir -p "$PROJECT_DIR"
cd "$PROJECT_DIR"
lake init "$PROJECT_NAME"
cd .. 

# Create additional folder structure in the project module directory
echo "Creating folder structure (proof, specs, ffi, tests) in $MODULE_NAME/..."
mkdir -p "$PROJECT_DIR/$MODULE_NAME/proof"
mkdir -p "$PROJECT_DIR/$MODULE_NAME/specs"
mkdir -p "$PROJECT_DIR/$MODULE_NAME/ffi"
mkdir -p "$PROJECT_DIR/$MODULE_NAME/tests"

# Create module files that import the respective modules
touch "$PROJECT_DIR/$MODULE_NAME/Proof.lean"
touch "$PROJECT_DIR/$MODULE_NAME/Specs.lean"
touch "$PROJECT_DIR/$MODULE_NAME/FFI.lean"
touch "$PROJECT_DIR/$MODULE_NAME/Tests.lean"

# Delete the Basic.lean file that lake init creates
rm -f "$PROJECT_DIR/$MODULE_NAME/Basic.lean"

# Update the root ModuleName.lean file to import all modules
cat > "$PROJECT_DIR/$MODULE_NAME.lean" << EOF
import $MODULE_NAME.Proof
import $MODULE_NAME.Specs
import $MODULE_NAME.FFI
import $MODULE_NAME.Tests
EOF

# Update Main.lean to just print "Hello, World!"
cat > "$PROJECT_DIR/Main.lean" << EOF
def main : IO Unit := do
  IO.println "Hello, World!"
EOF

# removing the git artifacts after initialization
rm -rf "$PROJECT_DIR/.github"

echo ""
echo "✓ Project '$PROJECT_NAME' created successfully!"
echo ""
echo "Next steps:"
echo "1. cd $PROJECT_DIR"
echo "2. lake build    # Build the project"
echo "3. lake run      # Run the executable"
