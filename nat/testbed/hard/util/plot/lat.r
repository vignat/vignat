library(plyr)
library(ggplot2)

all_data <- data.frame(V1=integer(), V2=integer(),
                       V3=integer(), V4=integer(),
                       V5=integer(),
                       middlebox=character())

netfilter <- read.table("nf-latency.txt")
netfilter["middlebox"] <- "NetFilter"
vignat <- read.table("vignat-latency.txt")
vignat["middlebox"] <- "VigNAT"
#nop <- read.table("nop-thru-lat.txt")
#nop["middlebox"] <- "NOP"
#unverified <- read.table("unverified-thru-lat.txt")
#unverified["middlebox"] <- "DPDK-unverified"

all_data <- rbind(all_data, netfilter)
all_data <- rbind(all_data, vignat)
#all_data <- rbind(all_data, nop)
#all_data <- rbind(all_data, unverified)

cbbPalette <- c("#000000", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

pd <- position_dodge(1)

p <- ggplot(all_data, aes(x=V1/1000, y=V4/1e6,
                          group=middlebox,
                          color=middlebox,
                          shape=middlebox)) +
     geom_point(size=3,position=pd) +
     geom_line() +
     geom_errorbar(aes(ymin=(V4-V5)/1e6, ymax=(V4+V5)/1e6), width=.01,
                   position=pd) +
     labs(title="1 way latency for 100Kpkt/s. No churns") +
     xlab("# concurrent flows (K)") +
     ylab(bquote("1-way latency, ms")) +
     theme_bw() +
     expand_limits(x=0,y=0) +
     coord_cartesian(ylim=c(0,2)) +
     theme( plot.margin = unit( c(0,0,0,0) , "in" ) )

ggsave(filename="latency.png")
print(p)