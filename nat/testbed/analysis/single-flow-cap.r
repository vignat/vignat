
source("plot.r")

comp_deps <- plot_missrates(load_missrates(c("resk1", "resk160k")))

ggsave(filename="single_flow_cap.pdf", plot=comp_deps)