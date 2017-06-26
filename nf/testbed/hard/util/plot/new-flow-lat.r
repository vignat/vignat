library(plyr)
library(ggplot2)
library(scales)

all_data <- data.frame(V1=integer(), V2=integer(),
                       V3=integer(), V4=integer(),
                       middlebox=character())

netfilter <- read.table("netfilter-new-flows-latency.txt")
netfilter["middlebox"] <- "NetFilter"
vignat <- read.table("vignat-new-flows-latency.txt")
vignat["middlebox"] <- "VigNAT"
vignat2 <- read.table("vignat-twice-new-flows-latency.txt")
vignat2["middlebox"] <- "VigNAT (2x bigger table)"
unverified <- read.table("unverified-new-flows-latency.txt")
unverified["middlebox"] <- "DPDK-unverified"
counted <- read.table("counted-chains-new-flows-latency.txt")
counted["middlebox"] <- "Counted-chains map"

all_data <- rbind(all_data, netfilter)
#all_data <- rbind(all_data, vignat)
#all_data <- rbind(all_data, vignat2)
all_data <- rbind(all_data, unverified)
all_data <- rbind(all_data, counted)

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
     labs(title="1 way latency for ~8Kpkt/s. 1000 sample new flows") +
     xlab("# concurrent flows (K)") +
     ylab(bquote("1-way latency, " * mu * "s")) +
     theme_bw() +
     expand_limits(x=0,y=1) +
     #scale_y_log10(breaks = trans_breaks("log10", function(x) 10^x),
     #              labels = trans_format("log10", math_format(10^.x))) +
     coord_cartesian(ylim=c(0,25)) +
     theme( plot.margin = unit( c(0,0,0,0) , "in" ) )

ggsave(filename="new-flow-latency.png")
print(p)