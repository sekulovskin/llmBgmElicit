% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/callPriorElicitVariations.R
\name{callPriorElicitVariations}
\alias{callPriorElicitVariations}
\title{Compare Prompt Variants for LLM-Based Prior Elicitation}
\usage{
callPriorElicitVariations(target_fun, prompt_specs, ...)
}
\arguments{
\item{target_fun}{A function used for prior elicitation, such as
\code{elicitEdgeProbLite}, or \code{elicitEdgeProb}.}

\item{prompt_specs}{A list of prompt specifications. Each element must be a list containing
\code{system} and \code{user} character strings used to construct prompts.}

\item{...}{Additional arguments passed to the target function. These typically include
\code{context}, \code{variable_list}, \code{LLM_model}, \code{n_rep} or \code{n_perm}, and other settings.}
}
\value{
A list with the following elements:
\describe{
\item{\code{summary}}{A data frame summarizing the results across prompt variants, including
the mean and standard deviation of the prior probabilities for each variable pair.}
\item{\code{raw_outputs}}{A list of full outputs returned by the target function for each prompt variant.}
\item{\code{prompts}}{The list of prompt specifications used.}
}
}
\description{
This function evaluates multiple prompt variants by repeatedly calling a given LLM-based
prior elicitation function (e.g.,\code{elicitEdgeProbLite}, or \code{elicitEdgeProb})
using different user/system prompt pairs. It returns a summary of mean and standard deviation
in the estimated edge inclusion probabilities across prompt variants.
}
\details{
Each prompt variant is evaluated independently by calling the selected prior elicitation
function once with that prompt. The resulting edge probabilities are aggregated across
prompt variants and summarized with means and standard deviations.

This function is useful for testing the sensitivity of prior elicitation to different
LLM prompt formulations.
}
\examples{
\dontrun{
prompt_variants <- list(
  list(system = "You are an expert...", user = "Decide if x and y are conditionally related."),
  list(system = "You are a statistical analyst...", user = "Should x and y have an edge?")
)

result <- callPriorElicitVariations(
  target_fun = llmPriorElicitSimple,
  prompt_specs = prompt_variants,
  context = "Study on well-being and lifestyle",
  variable_list = c("Sleep", "Mood", "Exercise"),
  n_rep = 2
)

print(result$summary)
}

}
