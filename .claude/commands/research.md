---
name: research
description: Research a GitHub repository, project, or academic paper and save findings to docs/research/
arguments:
  - name: target
    description: Repository (owner/repo), project name, paper title, or arXiv ID to research
    required: true
---

# Research: $ARGUMENTS.target

Research the specified target thoroughly and create comprehensive documentation.

## Determine Research Type

First, identify what kind of target this is:
- **GitHub Repository**: Contains `/` (e.g., `owner/repo`) or mentions GitHub
- **arXiv Paper**: Starts with numbers like `2301.12345` or mentions arXiv
- **Paper Title**: Quoted text or mentions "paper", "論文"
- **Project/Topic**: General topic or project name

## Instructions for Repository/Project

1. Use the research skill to investigate **$ARGUMENTS.target**
2. Gather information through:
   - Web search for general information
   - GitHub repository inspection via `gh` and WebFetch
   - Source code analysis by cloning to `/tmp/<name>-research`
   - Reading key files (README, source code, config files)
   - Author's blog posts or related documentation

3. Create a comprehensive markdown report covering:
   - Overview (repo link, author, license, language, stats)
   - Features and syntax examples
   - Architecture and design
   - Implementation details
   - Related projects
   - Sources with links

## Instructions for Academic Paper

1. Use the research skill to investigate **$ARGUMENTS.target**
2. Gather information through:
   - Web search to find the paper (arXiv, ACM, IEEE, etc.)
   - WebFetch to get abstract and metadata
   - Download PDF via wget if needed: `wget -O /tmp/paper.pdf <url>`
   - Read PDF with Read tool for detailed content
   - Search for related resources (slides, blog posts, implementations)

3. Create a comprehensive markdown report covering:
   - Metadata (authors, venue, year, links)
   - Abstract (quoted)
   - Problem statement and motivation
   - Key contributions
   - Approach/Method
   - Key concepts and definitions
   - Results
   - Implementation details (if available)
   - Limitations and future work
   - Sources with links

## Save Location

Save the report to `docs/research/<name>.md`
- For repos: use repository name (e.g., `malgo.md`)
- For papers: use short descriptive name (e.g., `sequent-calculus-pl.md`)

## Output

After completing the research, inform the user:
- Where the report was saved
- Key highlights from the research
