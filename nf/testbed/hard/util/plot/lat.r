library(plyr)
library(ggplot2)

all_data <- data.frame(V1=integer(), V2=integer(),
                       V3=integer(), V4=integer(),
                       middlebox=character())

netfilter <- read.table("netfilter-latency.txt")
netfilter["middlebox"] <- "NetFilter"
vignat <- read.table("vignat-latency.txt")
vignat["middlebox"] <- "VigNAT"
counted_chains <- read.table("counted-chains-latency.txt")
counted_chains ["middlebox"] <- "counted-chains"
nop <- read.table("nop-latency.txt")
nop["middlebox"] <- "NOP"
unverified <- read.table("unverified-latency.txt")
unverified["middlebox"] <- "DPDK-unverified"

all_data <- rbind(all_data, netfilter)
all_data <- rbind(all_data, vignat)
all_data <- rbind(all_data, counted_chains)
all_data <- rbind(all_data, nop)
all_data <- rbind(all_data, unverified)

cbbPalette <- c("#000000", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

pd <- position_dodge(2)

p <- ggplot(all_data, aes(x=V1/1e3, y=V3/1e3,
                          group=middlebox,
                          color=middlebox,
                          shape=middlebox)) +
     geom_point(size=3,position=pd) +
     geom_line() +
     geom_errorbar(aes(ymin=(V3-V4)/1e3, ymax=(V3+V4)/1e3), width=.01,
                   position=pd) +
     labs(title="1 way latency for ~8Kpkt/s. No churns") +
     xlab("# concurrent flows (K)") +
     ylab(bquote("1-way latency, "+mu+"s")) +
     theme_bw() +
     expand_limits(x=0,y=0) +
     coord_cartesian(ylim=c(0,25)) +
     theme( plot.margin = unit( c(0,0,0,0) , "in" ) )

ggsave(filename="latency.png")
print(p)