library(plyr)
library(ggplot2)

all_data <- data.frame(V1=integer(), V2=integer(),
                       V3=integer(), V4=integer(),
                       middlebox=character())

net_filter <- read.table("netfilter-rr.txt")
net_filter["middlebox"] <- "NetFilter"
alpha_better_hash <- read.table("better-hash-rr.txt")
alpha_better_hash["middlebox"] <- "alpha-good-hash"
noop <- read.table("noop-rr.txt")
noop["middlebox"] <- "no-op"

all_data <- rbind(all_data, net_filter)
all_data <- rbind(all_data, alpha_better_hash)
all_data <- rbind(all_data, noop)

cbbPalette <- c("#000000", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

pd <- position_dodge(600)

p <- ggplot(all_data, aes(x=V1, y=V3,
                          group=middlebox,
                          color=middlebox,
                          shape=middlebox)) +
     geom_point(size=3,position=pd) +
     geom_line() +
     geom_errorbar(aes(ymin=V3-V4, ymax=V3+V4), width=.01,
                   position=pd) +
     labs(title="2 way latency for netperf request-response test. No churns") +
     xlab("# concurrent flows") +
     ylab(bquote("2-way latency," * mu * "s")) +
     theme_bw() +
     expand_limits(x=0,y=0) +
     coord_cartesian(ylim=c(0,300)) +
     theme( plot.margin = unit( c(0,0,0,0) , "in" ) )

ggsave(filename="request-responce.png")
print(p)