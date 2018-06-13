// C# script to replicate coverage info from Table one, based on a 'run.istats' file of the KLEE output.

﻿using System;
using System.Collections.Generic;
using System.IO;

namespace InstrCounter
{
    class Program
    {
        static void Main(string[] args)
        {
            string currentFunctionName = null;
            var counts = new Dictionary<string, (int, int)>();
            var lines = new HashSet<int>();
            var covered = 0;
            var uncovered = 0;
            var ignoreNext = false;
            foreach (var line in File.ReadLines("run.istats"))
            {
                if (ignoreNext)
                {
                    ignoreNext = false;
                    continue;
                }

                var parts = line.Split(" ");

                if (line.StartsWith("fn="))
                {
                    if (currentFunctionName != null)
                    {
                        counts.Add(currentFunctionName, (covered, uncovered));
                        covered = 0;
                        uncovered = 0;
                        lines = new HashSet<int>();
                        currentFunctionName = null;
                    }

                    currentFunctionName = line.Substring(3);

                    continue;
                }
                else if (line.StartsWith("calls="))
                {
                    // next is inclusive cost
                    ignoreNext = true;
                    continue;
                }
                else if (line.StartsWith("cfn=") || line.StartsWith("cfl=") || line.StartsWith("fl="))
                {
                    continue; // Ignore, in the middle of a fn=
                }
                else if (!int.TryParse(parts[0], out int ignored))
                {
                    // OK...
                    Console.WriteLine("SKIP: " + line);
                    continue;
                }

                var lineNumber = int.Parse(parts[0]);
                var lineCovered = int.Parse(parts[2]);
                var lineUncovered = int.Parse(parts[10]);

                if (lines.Add(lineNumber)) // only count a single instr per line
                {
                    covered += lineCovered;
                    uncovered += lineUncovered;
                }
            }

            var vignat = (0, 0);
            var dpdk = (0, 0);
            var ixgbe = (0, 0);

            foreach (var (name, (cov, uncov)) in counts)
            {
                if (name.StartsWith("ixgbe_") || name.StartsWith("ixgbevf_"))
                {
                    ixgbe = (ixgbe.Item1 + cov, ixgbe.Item2 + uncov);
                }
                else if (name.StartsWith("rte_") || name.StartsWith("vdev_") || name.StartsWith("pci_") || name.StartsWith("eal_")
                      || name.StartsWith("memzone_") || name.StartsWith("_rte") || name.StartsWith("__rte"))
                {
                    dpdk = (dpdk.Item1 + cov, dpdk.Item2 + uncov);
                }
                else if (name.StartsWith("nf_") || name.StartsWith("nat_")
                    || name == "lcore_main" || name == "main"
                    || name == "allocate_flowmanager" || name == "allocate_flow" || name == "get_and_rejuvenate" || name == "get_flow_by_int_key"
                    || name == "get_flow_by_ext_key" || name == "expire_flows" || name == "get_flow" || name == "get_flow_int" || name == "get_flow_ext"
                    || name == "fill_int_key" || name == "fill_ext_key" || name == "add_flow" || name == "allocate_flowtables")
                {
                    vignat = (vignat.Item1 + cov, vignat.Item2 + uncov);
                }
                else
                {
                    Console.WriteLine("IGNORE: " + name);
                }
            }

            Console.WriteLine($"VigNAT: {vignat.Item1} covered, {vignat.Item2} uncovered, {vignat.Item1 + vignat.Item2} total");
            Console.WriteLine($"DPDK: {dpdk.Item1} covered, {dpdk.Item2} uncovered, {dpdk.Item1 + dpdk.Item2} total");
            Console.WriteLine($"ixgbe: {ixgbe.Item1} covered, {ixgbe.Item2} uncovered, {ixgbe.Item1 + ixgbe.Item2} total");
            Console.Read();
        }
    }
}
