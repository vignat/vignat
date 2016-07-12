
source("plot.r")

comp_deps <- plot_missrates(load_missrates(c("mynat", "router", "direct", "netfilter", "no-lookup")))

ggsave(filename="single_flow_nf_direct.pdf", plot=comp_deps)