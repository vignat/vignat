library(plyr)
library(ggplot2)

all_data <- data.frame(V1=integer(), V2=integer(),
                       V3=integer(),
                       middlebox=character())

#vignat <- read.table("vignat-lat-rate.txt")
#vignat["middlebox"] <- "vignat"
netfilter <- read.table("nf-lat-rate.txt")
netfilter["middlebox"] <- "netfilter"

#all_data <- rbind(all_data, vignat)
all_data <- rbind(all_data, netfilter)

cbbPalette <- c("#000000", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

pd <- position_dodge(1)

p <- ggplot(all_data, aes(x=V1, y=V2/1e3)) +
     geom_point(size=3) +
     geom_line() +
     geom_errorbar(aes(ymin=(V2-V3)/1e3, ymax=(V2+V3)/1e3), width=.01) +
     labs(title="1 way latency for MoonGen high load test, single flow") +
     xlab("rate (Mbps)") +
     ylab(bquote("1-way latency, microsec")) +
     theme_bw() +
     expand_limits(x=0,y=0) +
     theme( plot.margin = unit( c(0,0,0,0) , "in" ) )

ggsave(filename="lll.png")
print(p)