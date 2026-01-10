terraform {
  required_providers {
    github = {
      source  = "integrations/github"
      version = "~> 6.0"
    }
  }
}

provider "github" {
  owner = "takoeight0821"
}

# Install the Renovate app on the ziku repository
resource "github_app_installation_repository" "renovate_ziku" {
  # The installation ID from the GitHub App installation
  installation_id = var.renovate_app_installation_id
  repository      = "ziku"
}

variable "renovate_app_installation_id" {
  description = "The installation ID of the Renovate GitHub App"
  type        = string
}
