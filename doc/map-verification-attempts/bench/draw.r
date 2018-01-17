library(ggplot2)
library(scales)
perf_times <- read.table("export.csv", header=TRUE, sep=",")
p <- ggplot(perf_times, aes(x=hitrate, y=val, fill=type)) + 
  geom_bar(position=position_dodge(), stat="identity") + 
  geom_errorbar(position=position_dodge(), aes(ymin=val-2*sigma, ymax=val+2*sigma)) +
  facet_grid(load ~ pg,labeller = label_both) + scale_y_continuous(trans=log2_trans()) +
  xlab("Hit rate") + ylab("execution time") +
  ggtitle("Hash map implementations performance")
  
ggsave("perfplot.png", plot = p, width = 5, height=5)
quit()