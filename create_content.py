import json
from collections import namedtuple

# Define a named tuple class
Declaration = namedtuple('Declaration', ['name', 'type', 'label', 'statement', 'proof', 'dependencies'])

def get_label_from_docstring(docstring):
    lines = docstring.split('\n')
    lines = [line.strip() for line in lines]
    lines = [line for line in lines if line.startswith(r'\label{')]
    assert len(lines) == 1, f'Expected exactly one line starting with \label{{, got {len(lines)}'
    line = lines[0]
    label = line.split('{')[1]
    return label

def get_type_from_docstring(docstring):
    lines = docstring.split('\n')
    lines = [line.strip() for line in lines]
    lines = [line for line in lines if line.startswith(r'\begin{')]
    assert lines.length in {1, 2}, f'Expected exactly one or two lines starting with \begin{{, got {len(lines)}'
    line = lines[0]
    type = line.split('{')[1]
    return type

def short_type(type):
    if type == "theorem":
        return "thm"

    if type == "lemma":
        return "lem"
    
    if type == "definition":
        return "def"
    
    assert False, f'Unknown type {type}'

def auto_label(name, type):
    return f'{short_type(type)}:{name}'


# Default docstring
with open('template.tex') as f:
    default_docstring = f.read()

# Declarations and their docstrings and dependencies
with open('blueprintDecls.json') as f:
    data = json.load(f)

# Holds the declarations
decls = []

for item in data:
    decl = Declaration(name=item[0], docstring=item[1], type=None, label=None, dependencies=item[2])

    if decl.docstring is None:
        decl.type = 'theorem'
        decl.label = auto_label(decl.name, decl.type)
        decl.docstring = 
        pass
    print(item)
    break

"""
\begin{theorem}
    \label{thm:pythagoras}
    The square of the hypotenuse of a right triangle is equal to the sum of the squares of the other two sides.
\end{theorem}
\begin{proof}
    This is a proof.
\end{proof}

"""