---
name: research
description: Research a GitHub repository, software project, or academic paper in depth. Use when the user asks to "research", "investigate", "analyze", or "study" a repository, library, framework, programming language project, or academic paper. Produces a comprehensive markdown report saved to docs/research/.
---

# Research Skill - Repository, Project & Paper Analysis

Conduct in-depth research on GitHub repositories, software projects, and academic papers, producing comprehensive markdown documentation.

## When to Use

- User asks to "research", "investigate", or "analyze" a GitHub repository
- User wants to understand a programming language, library, or framework
- User needs documentation about a project's architecture or implementation
- User asks to research an academic paper (arXiv, conference paper, journal article)
- User wants to understand a theoretical concept or algorithm from literature

## Research Workflow (GitHub Repository)

### 1. Initial Discovery

Use WebSearch to find general information:
```
WebSearch: "<project-name> GitHub programming language"
WebSearch: "<owner>/<repo> architecture implementation"
```

### 2. Fetch Repository Overview

Use WebFetch on the GitHub repository page:
```
WebFetch: https://github.com/<owner>/<repo>
Prompt: "Provide comprehensive overview including purpose, features, implementation language, and architecture"
```

### 3. Get Repository Metadata

Use `gh` command for structured data:
```bash
gh repo view <owner>/<repo> --json name,description,url,stargazerCount,forkCount,primaryLanguage,languages,repositoryTopics,createdAt,updatedAt
```

### 4. Clone and Explore Source Code

Clone to a temporary directory for deep analysis:
```bash
cd /tmp && rm -rf <repo>-research 2>/dev/null
git clone --depth 1 https://github.com/<owner>/<repo>.git <repo>-research
```

Then explore the structure:
```bash
ls /tmp/<repo>-research/
ls /tmp/<repo>-research/src/  # or relevant source directory
```

### 5. Read Key Files

Use the Read tool to examine:
- `README.md` - Project overview and usage
- Main source files - Core implementation
- Configuration files (`package.json`, `Cargo.toml`, `*.cabal`, etc.)
- Example files - Usage patterns

### 6. Search for Technical Details

Look for:
- Architecture patterns (compiler phases, IR definitions, etc.)
- Key data structures and types
- API design and interfaces
- Build system and dependencies

### 7. Find Related Resources

Search for author's blog posts, documentation, or related projects:
```
WebSearch: "<author> <project> blog"
WebSearch: "site:<author-blog> <project>"
```

## Research Workflow (Academic Paper)

### 1. Find the Paper

Use WebSearch to locate the paper:
```
WebSearch: "<paper title>" arXiv OR ACM OR IEEE
WebSearch: "<author name>" "<topic>" paper
WebSearch: "<paper title>" PDF
```

Common paper repositories:
- **arXiv**: `https://arxiv.org/abs/<id>` (e.g., `2301.12345`)
- **ACM DL**: `https://dl.acm.org/doi/<doi>`
- **IEEE Xplore**: `https://ieeexplore.ieee.org/document/<id>`
- **Semantic Scholar**: `https://www.semanticscholar.org/paper/<id>`

### 2. Fetch Paper Content

Use WebFetch to get the paper abstract and metadata:
```
WebFetch: https://arxiv.org/abs/<id>
Prompt: "Extract title, authors, abstract, and key contributions"
```

For arXiv, the HTML abstract page is more accessible than PDF:
```
WebFetch: https://arxiv.org/abs/2301.12345
```

### 3. Download PDF (Optional)

Download the PDF for detailed reading using wget:
```bash
# arXiv
wget -O /tmp/paper.pdf https://arxiv.org/pdf/2301.12345.pdf

# ACM (if open access)
wget -O /tmp/paper.pdf "https://dl.acm.org/doi/pdf/<doi>"
```

Then use Read tool to view the PDF:
```
Read: /tmp/paper.pdf
```

Note: PDF reading extracts text and may lose some formatting. For complex formulas or figures, refer to the original PDF.

### 4. Search for Related Resources

Find supplementary materials:
```
WebSearch: "<paper title>" implementation GitHub
WebSearch: "<paper title>" slides presentation
WebSearch: "<author>" "<paper title>" blog
WebSearch: "<paper title>" explained tutorial
```

### 5. Find Citing/Related Papers

Search for papers that cite or relate to this work:
```
WebSearch: "<paper title>" cited by
WebSearch: "<key concept from paper>" survey
```

### 6. Gather Implementation Details

If the paper has associated code:
- Check paper's GitHub link
- Search for reference implementations
- Look for reproductions by others

## Output Format (Repository)

Create a markdown document with the following structure:

```markdown
# <Project Name>: <Tagline>

## Overview
- Repository link
- Author
- License
- Implementation language
- Key stats (stars, etc.)

## Features
- Language/library features
- Syntax examples (if applicable)

## Architecture
- System design
- Key components
- Data flow / compilation pipeline

## Implementation Details
- Technologies used
- Notable design decisions

## Related Projects
- Other work by the author
- Similar projects

## Sources
- Links to all referenced materials
```

## Output Format (Academic Paper)

Create a markdown document with the following structure:

```markdown
# <Paper Title>

## Metadata
- **Authors**: Author1, Author2, ...
- **Published**: Venue, Year
- **Links**: [arXiv](url) | [PDF](url) | [Code](url)

## Abstract
> Original abstract quoted here

## Problem Statement
What problem does this paper address? Why is it important?

## Key Contributions
1. Contribution 1
2. Contribution 2
3. ...

## Approach / Method
How do they solve the problem? Key techniques and algorithms.

## Key Concepts
Define important terms and concepts introduced or used in the paper.

## Results
Main experimental results or theoretical findings.

## Related Work
How does this relate to other work in the field?

## Implementation
- Reference implementation (if available)
- Key data structures and algorithms
- Complexity analysis

## Limitations & Future Work
What are the limitations? What do the authors suggest for future work?

## Personal Notes
Your observations, questions, and connections to other work.

## Sources
- Paper link
- Supplementary materials
- Related blog posts or explanations
```

## Saving the Report

Always save to `docs/research/<project-name>.md`:
```bash
mkdir -p docs/research
```

Then use Write tool to create the file.

## Tips

### For Repositories
- For compilers/languages: Focus on IR design, type system, compilation phases
- For libraries: Focus on API design, usage patterns, performance characteristics
- For frameworks: Focus on architecture, extension points, conventions
- Note any planned/WIP features mentioned in the codebase

### For Academic Papers
- For theoretical papers: Focus on definitions, theorems, and proofs
- For systems papers: Focus on architecture, implementation, and evaluation
- For PL papers: Focus on syntax, semantics, type system, and metatheory
- For algorithm papers: Focus on correctness, complexity, and practical considerations
- Quote key definitions and theorems verbatim when important
- Note connections to other papers or techniques you know

### General
- Always cite sources with markdown links
- Include code examples when they help explain concepts
- Use diagrams (ASCII or mermaid) for complex relationships
- Distinguish between your interpretation and the original content
