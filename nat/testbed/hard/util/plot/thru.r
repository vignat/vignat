library(plyr)
library(ggplot2)

all_data <- data.frame(V1=integer(), V2=integer(),
                       V3=integer(), V4=integer(),
                       V5=integer(),
                       middlebox=character())

netfilter <- read.table("netfilter-mf-find-mg-1p.txt")
netfilter["middlebox"] <- "NetFilter"
vignat <- read.table("vignat-mf-find-mg-1p.txt")
vignat["middlebox"] <- "VigNAT"
counted_chains <- read.table("counted-chains-mf-find-mg-1p.txt")
counted_chains ["middlebox"] <- "counted-chains"
nop <- read.table("nop-mf-find-mg-1p.txt")
nop["middlebox"] <- "NOP"
unverified <- read.table("unverified-mf-find-mg-1p.txt")
unverified["middlebox"] <- "DPDK-unverified"

all_data <- rbind(all_data, netfilter)
all_data <- rbind(all_data, counted_chains)
all_data <- rbind(all_data, vignat)
all_data <- rbind(all_data, nop)
all_data <- rbind(all_data, unverified)

cbbPalette <- c("#000000", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

p <- ggplot(all_data, aes(x=V1/1000, y=V4/1e6,
                          group=middlebox,
                          color=middlebox,
                          shape=middlebox)) +
     geom_line(size=1) +
     labs(title="Loopback throughput, 1% packets lost") +
     xlab("# concurrent flows (K)") +
     ylab(bquote("Throughput Mpkt/s")) +
     theme_bw() +
     expand_limits(x=0,y=0)

ggsave(filename="thru.png")
print(p)