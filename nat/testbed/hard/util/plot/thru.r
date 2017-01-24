library(plyr)
library(ggplot2)

all_data <- data.frame(V1=integer(), V2=integer(),
                       V3=integer(), V4=integer(),
                       V5=integer(),
                       middlebox=character())

alpha_better_hash <- read.table("better-hash-throughput.txt")
alpha_better_hash["middlebox"] <- "alpha-good-hash"
alpha_old_hash <- read.table("old-hash-throughput.txt")
alpha_old_hash["middlebox"] <- "alpha-old-hash"
#net_filter <- read.table("net-filter-throughput.txt")
#net_filter["middlebox"] <- "NetFilter"

all_data <- rbind(all_data, alpha_better_hash)
all_data <- rbind(all_data, alpha_old_hash)
#all_data <- rbind(all_data, net_filter)

cbbPalette <- c("#000000", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

p <- ggplot(all_data, aes(x=V1, y=V5/1e6,
                          group=middlebox,
                          color=middlebox,
                          shape=middlebox)) +
     geom_line(size=1) +
     labs(title="Loopback throughput, 64B packets") +
     xlab("# concurrent flows") +
     ylab(bquote("Throughput Mpkt/s")) +
     theme_bw() +
     expand_limits(x=0,y=0) +
     geom_jitter(height=0,width=100)

ggsave(filename="thru.png")
print(p)