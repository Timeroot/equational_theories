# Extraction diagnostics

[Main audit](../definability_open_audit.md).

This is a complete warning list, not the CLI’s first-four preview.

## Implication scan

Counts: `{"conjecture": 27, "facts": 1631, "implication": 10772, "unconditional": 1}`.

Unparsed attributed statements: 0.


### Attributed source files outside the Definability import closure

These are not claimed checked by the Definability entry-point build alone.

- [equational_theories/Asterix.lean](../../equational_theories/Asterix.lean)
- [equational_theories/CentralGroupoids.lean](../../equational_theories/CentralGroupoids.lean)
- [equational_theories/Confluence1.lean](../../equational_theories/Confluence1.lean)
- [equational_theories/Confluence2.lean](../../equational_theories/Confluence2.lean)
- [equational_theories/Confluence3.lean](../../equational_theories/Confluence3.lean)
- [equational_theories/Confluence4.lean](../../equational_theories/Confluence4.lean)
- [equational_theories/FiniteModel.lean](../../equational_theories/FiniteModel.lean)
- [equational_theories/Generated/All4x4Tables/Refutation0.lean](../../equational_theories/Generated/All4x4Tables/Refutation0.lean)
- [equational_theories/Generated/All4x4Tables/Refutation1.lean](../../equational_theories/Generated/All4x4Tables/Refutation1.lean)
- [equational_theories/Generated/All4x4Tables/Refutation10.lean](../../equational_theories/Generated/All4x4Tables/Refutation10.lean)
- [equational_theories/Generated/All4x4Tables/Refutation100.lean](../../equational_theories/Generated/All4x4Tables/Refutation100.lean)
- [equational_theories/Generated/All4x4Tables/Refutation101.lean](../../equational_theories/Generated/All4x4Tables/Refutation101.lean)
- [equational_theories/Generated/All4x4Tables/Refutation102.lean](../../equational_theories/Generated/All4x4Tables/Refutation102.lean)
- [equational_theories/Generated/All4x4Tables/Refutation103.lean](../../equational_theories/Generated/All4x4Tables/Refutation103.lean)
- [equational_theories/Generated/All4x4Tables/Refutation104.lean](../../equational_theories/Generated/All4x4Tables/Refutation104.lean)
- [equational_theories/Generated/All4x4Tables/Refutation105.lean](../../equational_theories/Generated/All4x4Tables/Refutation105.lean)
- [equational_theories/Generated/All4x4Tables/Refutation106.lean](../../equational_theories/Generated/All4x4Tables/Refutation106.lean)
- [equational_theories/Generated/All4x4Tables/Refutation107.lean](../../equational_theories/Generated/All4x4Tables/Refutation107.lean)
- [equational_theories/Generated/All4x4Tables/Refutation108.lean](../../equational_theories/Generated/All4x4Tables/Refutation108.lean)
- [equational_theories/Generated/All4x4Tables/Refutation109.lean](../../equational_theories/Generated/All4x4Tables/Refutation109.lean)
- [equational_theories/Generated/All4x4Tables/Refutation11.lean](../../equational_theories/Generated/All4x4Tables/Refutation11.lean)
- [equational_theories/Generated/All4x4Tables/Refutation110.lean](../../equational_theories/Generated/All4x4Tables/Refutation110.lean)
- [equational_theories/Generated/All4x4Tables/Refutation111.lean](../../equational_theories/Generated/All4x4Tables/Refutation111.lean)
- [equational_theories/Generated/All4x4Tables/Refutation112.lean](../../equational_theories/Generated/All4x4Tables/Refutation112.lean)
- [equational_theories/Generated/All4x4Tables/Refutation113.lean](../../equational_theories/Generated/All4x4Tables/Refutation113.lean)
- [equational_theories/Generated/All4x4Tables/Refutation114.lean](../../equational_theories/Generated/All4x4Tables/Refutation114.lean)
- [equational_theories/Generated/All4x4Tables/Refutation115.lean](../../equational_theories/Generated/All4x4Tables/Refutation115.lean)
- [equational_theories/Generated/All4x4Tables/Refutation116.lean](../../equational_theories/Generated/All4x4Tables/Refutation116.lean)
- [equational_theories/Generated/All4x4Tables/Refutation117.lean](../../equational_theories/Generated/All4x4Tables/Refutation117.lean)
- [equational_theories/Generated/All4x4Tables/Refutation118.lean](../../equational_theories/Generated/All4x4Tables/Refutation118.lean)
- [equational_theories/Generated/All4x4Tables/Refutation119.lean](../../equational_theories/Generated/All4x4Tables/Refutation119.lean)
- [equational_theories/Generated/All4x4Tables/Refutation12.lean](../../equational_theories/Generated/All4x4Tables/Refutation12.lean)
- [equational_theories/Generated/All4x4Tables/Refutation120.lean](../../equational_theories/Generated/All4x4Tables/Refutation120.lean)
- [equational_theories/Generated/All4x4Tables/Refutation121.lean](../../equational_theories/Generated/All4x4Tables/Refutation121.lean)
- [equational_theories/Generated/All4x4Tables/Refutation122.lean](../../equational_theories/Generated/All4x4Tables/Refutation122.lean)
- [equational_theories/Generated/All4x4Tables/Refutation123.lean](../../equational_theories/Generated/All4x4Tables/Refutation123.lean)
- [equational_theories/Generated/All4x4Tables/Refutation124.lean](../../equational_theories/Generated/All4x4Tables/Refutation124.lean)
- [equational_theories/Generated/All4x4Tables/Refutation125.lean](../../equational_theories/Generated/All4x4Tables/Refutation125.lean)
- [equational_theories/Generated/All4x4Tables/Refutation126.lean](../../equational_theories/Generated/All4x4Tables/Refutation126.lean)
- [equational_theories/Generated/All4x4Tables/Refutation127.lean](../../equational_theories/Generated/All4x4Tables/Refutation127.lean)
- [equational_theories/Generated/All4x4Tables/Refutation128.lean](../../equational_theories/Generated/All4x4Tables/Refutation128.lean)
- [equational_theories/Generated/All4x4Tables/Refutation129.lean](../../equational_theories/Generated/All4x4Tables/Refutation129.lean)
- [equational_theories/Generated/All4x4Tables/Refutation13.lean](../../equational_theories/Generated/All4x4Tables/Refutation13.lean)
- [equational_theories/Generated/All4x4Tables/Refutation130.lean](../../equational_theories/Generated/All4x4Tables/Refutation130.lean)
- [equational_theories/Generated/All4x4Tables/Refutation131.lean](../../equational_theories/Generated/All4x4Tables/Refutation131.lean)
- [equational_theories/Generated/All4x4Tables/Refutation132.lean](../../equational_theories/Generated/All4x4Tables/Refutation132.lean)
- [equational_theories/Generated/All4x4Tables/Refutation133.lean](../../equational_theories/Generated/All4x4Tables/Refutation133.lean)
- [equational_theories/Generated/All4x4Tables/Refutation134.lean](../../equational_theories/Generated/All4x4Tables/Refutation134.lean)
- [equational_theories/Generated/All4x4Tables/Refutation135.lean](../../equational_theories/Generated/All4x4Tables/Refutation135.lean)
- [equational_theories/Generated/All4x4Tables/Refutation136.lean](../../equational_theories/Generated/All4x4Tables/Refutation136.lean)
- [equational_theories/Generated/All4x4Tables/Refutation137.lean](../../equational_theories/Generated/All4x4Tables/Refutation137.lean)
- [equational_theories/Generated/All4x4Tables/Refutation138.lean](../../equational_theories/Generated/All4x4Tables/Refutation138.lean)
- [equational_theories/Generated/All4x4Tables/Refutation139.lean](../../equational_theories/Generated/All4x4Tables/Refutation139.lean)
- [equational_theories/Generated/All4x4Tables/Refutation14.lean](../../equational_theories/Generated/All4x4Tables/Refutation14.lean)
- [equational_theories/Generated/All4x4Tables/Refutation140.lean](../../equational_theories/Generated/All4x4Tables/Refutation140.lean)
- [equational_theories/Generated/All4x4Tables/Refutation141.lean](../../equational_theories/Generated/All4x4Tables/Refutation141.lean)
- [equational_theories/Generated/All4x4Tables/Refutation142.lean](../../equational_theories/Generated/All4x4Tables/Refutation142.lean)
- [equational_theories/Generated/All4x4Tables/Refutation143.lean](../../equational_theories/Generated/All4x4Tables/Refutation143.lean)
- [equational_theories/Generated/All4x4Tables/Refutation144.lean](../../equational_theories/Generated/All4x4Tables/Refutation144.lean)
- [equational_theories/Generated/All4x4Tables/Refutation145.lean](../../equational_theories/Generated/All4x4Tables/Refutation145.lean)
- [equational_theories/Generated/All4x4Tables/Refutation146.lean](../../equational_theories/Generated/All4x4Tables/Refutation146.lean)
- [equational_theories/Generated/All4x4Tables/Refutation147.lean](../../equational_theories/Generated/All4x4Tables/Refutation147.lean)
- [equational_theories/Generated/All4x4Tables/Refutation148.lean](../../equational_theories/Generated/All4x4Tables/Refutation148.lean)
- [equational_theories/Generated/All4x4Tables/Refutation149.lean](../../equational_theories/Generated/All4x4Tables/Refutation149.lean)
- [equational_theories/Generated/All4x4Tables/Refutation15.lean](../../equational_theories/Generated/All4x4Tables/Refutation15.lean)
- [equational_theories/Generated/All4x4Tables/Refutation150.lean](../../equational_theories/Generated/All4x4Tables/Refutation150.lean)
- [equational_theories/Generated/All4x4Tables/Refutation151.lean](../../equational_theories/Generated/All4x4Tables/Refutation151.lean)
- [equational_theories/Generated/All4x4Tables/Refutation152.lean](../../equational_theories/Generated/All4x4Tables/Refutation152.lean)
- [equational_theories/Generated/All4x4Tables/Refutation153.lean](../../equational_theories/Generated/All4x4Tables/Refutation153.lean)
- [equational_theories/Generated/All4x4Tables/Refutation154.lean](../../equational_theories/Generated/All4x4Tables/Refutation154.lean)
- [equational_theories/Generated/All4x4Tables/Refutation155.lean](../../equational_theories/Generated/All4x4Tables/Refutation155.lean)
- [equational_theories/Generated/All4x4Tables/Refutation156.lean](../../equational_theories/Generated/All4x4Tables/Refutation156.lean)
- [equational_theories/Generated/All4x4Tables/Refutation157.lean](../../equational_theories/Generated/All4x4Tables/Refutation157.lean)
- [equational_theories/Generated/All4x4Tables/Refutation158.lean](../../equational_theories/Generated/All4x4Tables/Refutation158.lean)
- [equational_theories/Generated/All4x4Tables/Refutation159.lean](../../equational_theories/Generated/All4x4Tables/Refutation159.lean)
- [equational_theories/Generated/All4x4Tables/Refutation16.lean](../../equational_theories/Generated/All4x4Tables/Refutation16.lean)
- [equational_theories/Generated/All4x4Tables/Refutation160.lean](../../equational_theories/Generated/All4x4Tables/Refutation160.lean)
- [equational_theories/Generated/All4x4Tables/Refutation161.lean](../../equational_theories/Generated/All4x4Tables/Refutation161.lean)
- [equational_theories/Generated/All4x4Tables/Refutation162.lean](../../equational_theories/Generated/All4x4Tables/Refutation162.lean)
- [equational_theories/Generated/All4x4Tables/Refutation163.lean](../../equational_theories/Generated/All4x4Tables/Refutation163.lean)
- [equational_theories/Generated/All4x4Tables/Refutation164.lean](../../equational_theories/Generated/All4x4Tables/Refutation164.lean)
- [equational_theories/Generated/All4x4Tables/Refutation165.lean](../../equational_theories/Generated/All4x4Tables/Refutation165.lean)
- [equational_theories/Generated/All4x4Tables/Refutation166.lean](../../equational_theories/Generated/All4x4Tables/Refutation166.lean)
- [equational_theories/Generated/All4x4Tables/Refutation167.lean](../../equational_theories/Generated/All4x4Tables/Refutation167.lean)
- [equational_theories/Generated/All4x4Tables/Refutation168.lean](../../equational_theories/Generated/All4x4Tables/Refutation168.lean)
- [equational_theories/Generated/All4x4Tables/Refutation169.lean](../../equational_theories/Generated/All4x4Tables/Refutation169.lean)
- [equational_theories/Generated/All4x4Tables/Refutation17.lean](../../equational_theories/Generated/All4x4Tables/Refutation17.lean)
- [equational_theories/Generated/All4x4Tables/Refutation170.lean](../../equational_theories/Generated/All4x4Tables/Refutation170.lean)
- [equational_theories/Generated/All4x4Tables/Refutation171.lean](../../equational_theories/Generated/All4x4Tables/Refutation171.lean)
- [equational_theories/Generated/All4x4Tables/Refutation172.lean](../../equational_theories/Generated/All4x4Tables/Refutation172.lean)
- [equational_theories/Generated/All4x4Tables/Refutation173.lean](../../equational_theories/Generated/All4x4Tables/Refutation173.lean)
- [equational_theories/Generated/All4x4Tables/Refutation174.lean](../../equational_theories/Generated/All4x4Tables/Refutation174.lean)
- [equational_theories/Generated/All4x4Tables/Refutation175.lean](../../equational_theories/Generated/All4x4Tables/Refutation175.lean)
- [equational_theories/Generated/All4x4Tables/Refutation176.lean](../../equational_theories/Generated/All4x4Tables/Refutation176.lean)
- [equational_theories/Generated/All4x4Tables/Refutation177.lean](../../equational_theories/Generated/All4x4Tables/Refutation177.lean)
- [equational_theories/Generated/All4x4Tables/Refutation178.lean](../../equational_theories/Generated/All4x4Tables/Refutation178.lean)
- [equational_theories/Generated/All4x4Tables/Refutation179.lean](../../equational_theories/Generated/All4x4Tables/Refutation179.lean)
- [equational_theories/Generated/All4x4Tables/Refutation18.lean](../../equational_theories/Generated/All4x4Tables/Refutation18.lean)
- [equational_theories/Generated/All4x4Tables/Refutation180.lean](../../equational_theories/Generated/All4x4Tables/Refutation180.lean)
- [equational_theories/Generated/All4x4Tables/Refutation181.lean](../../equational_theories/Generated/All4x4Tables/Refutation181.lean)
- [equational_theories/Generated/All4x4Tables/Refutation182.lean](../../equational_theories/Generated/All4x4Tables/Refutation182.lean)
- [equational_theories/Generated/All4x4Tables/Refutation183.lean](../../equational_theories/Generated/All4x4Tables/Refutation183.lean)
- [equational_theories/Generated/All4x4Tables/Refutation184.lean](../../equational_theories/Generated/All4x4Tables/Refutation184.lean)
- [equational_theories/Generated/All4x4Tables/Refutation185.lean](../../equational_theories/Generated/All4x4Tables/Refutation185.lean)
- [equational_theories/Generated/All4x4Tables/Refutation186.lean](../../equational_theories/Generated/All4x4Tables/Refutation186.lean)
- [equational_theories/Generated/All4x4Tables/Refutation187.lean](../../equational_theories/Generated/All4x4Tables/Refutation187.lean)
- [equational_theories/Generated/All4x4Tables/Refutation188.lean](../../equational_theories/Generated/All4x4Tables/Refutation188.lean)
- [equational_theories/Generated/All4x4Tables/Refutation189.lean](../../equational_theories/Generated/All4x4Tables/Refutation189.lean)
- [equational_theories/Generated/All4x4Tables/Refutation19.lean](../../equational_theories/Generated/All4x4Tables/Refutation19.lean)
- [equational_theories/Generated/All4x4Tables/Refutation190.lean](../../equational_theories/Generated/All4x4Tables/Refutation190.lean)
- [equational_theories/Generated/All4x4Tables/Refutation191.lean](../../equational_theories/Generated/All4x4Tables/Refutation191.lean)
- [equational_theories/Generated/All4x4Tables/Refutation192.lean](../../equational_theories/Generated/All4x4Tables/Refutation192.lean)
- [equational_theories/Generated/All4x4Tables/Refutation193.lean](../../equational_theories/Generated/All4x4Tables/Refutation193.lean)
- [equational_theories/Generated/All4x4Tables/Refutation194.lean](../../equational_theories/Generated/All4x4Tables/Refutation194.lean)
- [equational_theories/Generated/All4x4Tables/Refutation195.lean](../../equational_theories/Generated/All4x4Tables/Refutation195.lean)
- [equational_theories/Generated/All4x4Tables/Refutation196.lean](../../equational_theories/Generated/All4x4Tables/Refutation196.lean)
- [equational_theories/Generated/All4x4Tables/Refutation197.lean](../../equational_theories/Generated/All4x4Tables/Refutation197.lean)
- [equational_theories/Generated/All4x4Tables/Refutation198.lean](../../equational_theories/Generated/All4x4Tables/Refutation198.lean)
- [equational_theories/Generated/All4x4Tables/Refutation199.lean](../../equational_theories/Generated/All4x4Tables/Refutation199.lean)
- [equational_theories/Generated/All4x4Tables/Refutation2.lean](../../equational_theories/Generated/All4x4Tables/Refutation2.lean)
- [equational_theories/Generated/All4x4Tables/Refutation20.lean](../../equational_theories/Generated/All4x4Tables/Refutation20.lean)
- [equational_theories/Generated/All4x4Tables/Refutation200.lean](../../equational_theories/Generated/All4x4Tables/Refutation200.lean)
- [equational_theories/Generated/All4x4Tables/Refutation201.lean](../../equational_theories/Generated/All4x4Tables/Refutation201.lean)
- [equational_theories/Generated/All4x4Tables/Refutation202.lean](../../equational_theories/Generated/All4x4Tables/Refutation202.lean)
- [equational_theories/Generated/All4x4Tables/Refutation203.lean](../../equational_theories/Generated/All4x4Tables/Refutation203.lean)
- [equational_theories/Generated/All4x4Tables/Refutation204.lean](../../equational_theories/Generated/All4x4Tables/Refutation204.lean)
- [equational_theories/Generated/All4x4Tables/Refutation205.lean](../../equational_theories/Generated/All4x4Tables/Refutation205.lean)
- [equational_theories/Generated/All4x4Tables/Refutation206.lean](../../equational_theories/Generated/All4x4Tables/Refutation206.lean)
- [equational_theories/Generated/All4x4Tables/Refutation207.lean](../../equational_theories/Generated/All4x4Tables/Refutation207.lean)
- [equational_theories/Generated/All4x4Tables/Refutation208.lean](../../equational_theories/Generated/All4x4Tables/Refutation208.lean)
- [equational_theories/Generated/All4x4Tables/Refutation209.lean](../../equational_theories/Generated/All4x4Tables/Refutation209.lean)
- [equational_theories/Generated/All4x4Tables/Refutation21.lean](../../equational_theories/Generated/All4x4Tables/Refutation21.lean)
- [equational_theories/Generated/All4x4Tables/Refutation210.lean](../../equational_theories/Generated/All4x4Tables/Refutation210.lean)
- [equational_theories/Generated/All4x4Tables/Refutation211.lean](../../equational_theories/Generated/All4x4Tables/Refutation211.lean)
- [equational_theories/Generated/All4x4Tables/Refutation212.lean](../../equational_theories/Generated/All4x4Tables/Refutation212.lean)
- [equational_theories/Generated/All4x4Tables/Refutation213.lean](../../equational_theories/Generated/All4x4Tables/Refutation213.lean)
- [equational_theories/Generated/All4x4Tables/Refutation214.lean](../../equational_theories/Generated/All4x4Tables/Refutation214.lean)
- [equational_theories/Generated/All4x4Tables/Refutation215.lean](../../equational_theories/Generated/All4x4Tables/Refutation215.lean)
- [equational_theories/Generated/All4x4Tables/Refutation216.lean](../../equational_theories/Generated/All4x4Tables/Refutation216.lean)
- [equational_theories/Generated/All4x4Tables/Refutation217.lean](../../equational_theories/Generated/All4x4Tables/Refutation217.lean)
- [equational_theories/Generated/All4x4Tables/Refutation218.lean](../../equational_theories/Generated/All4x4Tables/Refutation218.lean)
- [equational_theories/Generated/All4x4Tables/Refutation219.lean](../../equational_theories/Generated/All4x4Tables/Refutation219.lean)
- [equational_theories/Generated/All4x4Tables/Refutation22.lean](../../equational_theories/Generated/All4x4Tables/Refutation22.lean)
- [equational_theories/Generated/All4x4Tables/Refutation220.lean](../../equational_theories/Generated/All4x4Tables/Refutation220.lean)
- [equational_theories/Generated/All4x4Tables/Refutation221.lean](../../equational_theories/Generated/All4x4Tables/Refutation221.lean)
- [equational_theories/Generated/All4x4Tables/Refutation222.lean](../../equational_theories/Generated/All4x4Tables/Refutation222.lean)
- [equational_theories/Generated/All4x4Tables/Refutation223.lean](../../equational_theories/Generated/All4x4Tables/Refutation223.lean)
- [equational_theories/Generated/All4x4Tables/Refutation224.lean](../../equational_theories/Generated/All4x4Tables/Refutation224.lean)
- [equational_theories/Generated/All4x4Tables/Refutation225.lean](../../equational_theories/Generated/All4x4Tables/Refutation225.lean)
- [equational_theories/Generated/All4x4Tables/Refutation226.lean](../../equational_theories/Generated/All4x4Tables/Refutation226.lean)
- [equational_theories/Generated/All4x4Tables/Refutation227.lean](../../equational_theories/Generated/All4x4Tables/Refutation227.lean)
- [equational_theories/Generated/All4x4Tables/Refutation228.lean](../../equational_theories/Generated/All4x4Tables/Refutation228.lean)
- [equational_theories/Generated/All4x4Tables/Refutation229.lean](../../equational_theories/Generated/All4x4Tables/Refutation229.lean)
- [equational_theories/Generated/All4x4Tables/Refutation23.lean](../../equational_theories/Generated/All4x4Tables/Refutation23.lean)
- [equational_theories/Generated/All4x4Tables/Refutation230.lean](../../equational_theories/Generated/All4x4Tables/Refutation230.lean)
- [equational_theories/Generated/All4x4Tables/Refutation231.lean](../../equational_theories/Generated/All4x4Tables/Refutation231.lean)
- [equational_theories/Generated/All4x4Tables/Refutation232.lean](../../equational_theories/Generated/All4x4Tables/Refutation232.lean)
- [equational_theories/Generated/All4x4Tables/Refutation233.lean](../../equational_theories/Generated/All4x4Tables/Refutation233.lean)
- [equational_theories/Generated/All4x4Tables/Refutation234.lean](../../equational_theories/Generated/All4x4Tables/Refutation234.lean)
- [equational_theories/Generated/All4x4Tables/Refutation235.lean](../../equational_theories/Generated/All4x4Tables/Refutation235.lean)
- [equational_theories/Generated/All4x4Tables/Refutation236.lean](../../equational_theories/Generated/All4x4Tables/Refutation236.lean)
- [equational_theories/Generated/All4x4Tables/Refutation237.lean](../../equational_theories/Generated/All4x4Tables/Refutation237.lean)
- [equational_theories/Generated/All4x4Tables/Refutation238.lean](../../equational_theories/Generated/All4x4Tables/Refutation238.lean)
- [equational_theories/Generated/All4x4Tables/Refutation239.lean](../../equational_theories/Generated/All4x4Tables/Refutation239.lean)
- [equational_theories/Generated/All4x4Tables/Refutation24.lean](../../equational_theories/Generated/All4x4Tables/Refutation24.lean)
- [equational_theories/Generated/All4x4Tables/Refutation240.lean](../../equational_theories/Generated/All4x4Tables/Refutation240.lean)
- [equational_theories/Generated/All4x4Tables/Refutation241.lean](../../equational_theories/Generated/All4x4Tables/Refutation241.lean)
- [equational_theories/Generated/All4x4Tables/Refutation242.lean](../../equational_theories/Generated/All4x4Tables/Refutation242.lean)
- [equational_theories/Generated/All4x4Tables/Refutation243.lean](../../equational_theories/Generated/All4x4Tables/Refutation243.lean)
- [equational_theories/Generated/All4x4Tables/Refutation244.lean](../../equational_theories/Generated/All4x4Tables/Refutation244.lean)
- [equational_theories/Generated/All4x4Tables/Refutation245.lean](../../equational_theories/Generated/All4x4Tables/Refutation245.lean)
- [equational_theories/Generated/All4x4Tables/Refutation246.lean](../../equational_theories/Generated/All4x4Tables/Refutation246.lean)
- [equational_theories/Generated/All4x4Tables/Refutation247.lean](../../equational_theories/Generated/All4x4Tables/Refutation247.lean)
- [equational_theories/Generated/All4x4Tables/Refutation248.lean](../../equational_theories/Generated/All4x4Tables/Refutation248.lean)
- [equational_theories/Generated/All4x4Tables/Refutation249.lean](../../equational_theories/Generated/All4x4Tables/Refutation249.lean)
- [equational_theories/Generated/All4x4Tables/Refutation25.lean](../../equational_theories/Generated/All4x4Tables/Refutation25.lean)
- [equational_theories/Generated/All4x4Tables/Refutation250.lean](../../equational_theories/Generated/All4x4Tables/Refutation250.lean)
- [equational_theories/Generated/All4x4Tables/Refutation251.lean](../../equational_theories/Generated/All4x4Tables/Refutation251.lean)
- [equational_theories/Generated/All4x4Tables/Refutation252.lean](../../equational_theories/Generated/All4x4Tables/Refutation252.lean)
- [equational_theories/Generated/All4x4Tables/Refutation253.lean](../../equational_theories/Generated/All4x4Tables/Refutation253.lean)
- [equational_theories/Generated/All4x4Tables/Refutation254.lean](../../equational_theories/Generated/All4x4Tables/Refutation254.lean)
- [equational_theories/Generated/All4x4Tables/Refutation255.lean](../../equational_theories/Generated/All4x4Tables/Refutation255.lean)
- [equational_theories/Generated/All4x4Tables/Refutation256.lean](../../equational_theories/Generated/All4x4Tables/Refutation256.lean)
- [equational_theories/Generated/All4x4Tables/Refutation257.lean](../../equational_theories/Generated/All4x4Tables/Refutation257.lean)
- [equational_theories/Generated/All4x4Tables/Refutation258.lean](../../equational_theories/Generated/All4x4Tables/Refutation258.lean)
- [equational_theories/Generated/All4x4Tables/Refutation259.lean](../../equational_theories/Generated/All4x4Tables/Refutation259.lean)
- [equational_theories/Generated/All4x4Tables/Refutation26.lean](../../equational_theories/Generated/All4x4Tables/Refutation26.lean)
- [equational_theories/Generated/All4x4Tables/Refutation260.lean](../../equational_theories/Generated/All4x4Tables/Refutation260.lean)
- [equational_theories/Generated/All4x4Tables/Refutation261.lean](../../equational_theories/Generated/All4x4Tables/Refutation261.lean)
- [equational_theories/Generated/All4x4Tables/Refutation262.lean](../../equational_theories/Generated/All4x4Tables/Refutation262.lean)
- [equational_theories/Generated/All4x4Tables/Refutation263.lean](../../equational_theories/Generated/All4x4Tables/Refutation263.lean)
- [equational_theories/Generated/All4x4Tables/Refutation264.lean](../../equational_theories/Generated/All4x4Tables/Refutation264.lean)
- [equational_theories/Generated/All4x4Tables/Refutation265.lean](../../equational_theories/Generated/All4x4Tables/Refutation265.lean)
- [equational_theories/Generated/All4x4Tables/Refutation266.lean](../../equational_theories/Generated/All4x4Tables/Refutation266.lean)
- [equational_theories/Generated/All4x4Tables/Refutation267.lean](../../equational_theories/Generated/All4x4Tables/Refutation267.lean)
- [equational_theories/Generated/All4x4Tables/Refutation268.lean](../../equational_theories/Generated/All4x4Tables/Refutation268.lean)
- [equational_theories/Generated/All4x4Tables/Refutation269.lean](../../equational_theories/Generated/All4x4Tables/Refutation269.lean)
- [equational_theories/Generated/All4x4Tables/Refutation27.lean](../../equational_theories/Generated/All4x4Tables/Refutation27.lean)
- [equational_theories/Generated/All4x4Tables/Refutation270.lean](../../equational_theories/Generated/All4x4Tables/Refutation270.lean)
- [equational_theories/Generated/All4x4Tables/Refutation271.lean](../../equational_theories/Generated/All4x4Tables/Refutation271.lean)
- [equational_theories/Generated/All4x4Tables/Refutation272.lean](../../equational_theories/Generated/All4x4Tables/Refutation272.lean)
- [equational_theories/Generated/All4x4Tables/Refutation273.lean](../../equational_theories/Generated/All4x4Tables/Refutation273.lean)
- [equational_theories/Generated/All4x4Tables/Refutation274.lean](../../equational_theories/Generated/All4x4Tables/Refutation274.lean)
- [equational_theories/Generated/All4x4Tables/Refutation275.lean](../../equational_theories/Generated/All4x4Tables/Refutation275.lean)
- [equational_theories/Generated/All4x4Tables/Refutation276.lean](../../equational_theories/Generated/All4x4Tables/Refutation276.lean)
- [equational_theories/Generated/All4x4Tables/Refutation277.lean](../../equational_theories/Generated/All4x4Tables/Refutation277.lean)
- [equational_theories/Generated/All4x4Tables/Refutation278.lean](../../equational_theories/Generated/All4x4Tables/Refutation278.lean)
- [equational_theories/Generated/All4x4Tables/Refutation279.lean](../../equational_theories/Generated/All4x4Tables/Refutation279.lean)
- [equational_theories/Generated/All4x4Tables/Refutation28.lean](../../equational_theories/Generated/All4x4Tables/Refutation28.lean)
- [equational_theories/Generated/All4x4Tables/Refutation280.lean](../../equational_theories/Generated/All4x4Tables/Refutation280.lean)
- [equational_theories/Generated/All4x4Tables/Refutation281.lean](../../equational_theories/Generated/All4x4Tables/Refutation281.lean)
- [equational_theories/Generated/All4x4Tables/Refutation282.lean](../../equational_theories/Generated/All4x4Tables/Refutation282.lean)
- [equational_theories/Generated/All4x4Tables/Refutation283.lean](../../equational_theories/Generated/All4x4Tables/Refutation283.lean)
- [equational_theories/Generated/All4x4Tables/Refutation284.lean](../../equational_theories/Generated/All4x4Tables/Refutation284.lean)
- [equational_theories/Generated/All4x4Tables/Refutation285.lean](../../equational_theories/Generated/All4x4Tables/Refutation285.lean)
- [equational_theories/Generated/All4x4Tables/Refutation286.lean](../../equational_theories/Generated/All4x4Tables/Refutation286.lean)
- [equational_theories/Generated/All4x4Tables/Refutation287.lean](../../equational_theories/Generated/All4x4Tables/Refutation287.lean)
- [equational_theories/Generated/All4x4Tables/Refutation288.lean](../../equational_theories/Generated/All4x4Tables/Refutation288.lean)
- [equational_theories/Generated/All4x4Tables/Refutation289.lean](../../equational_theories/Generated/All4x4Tables/Refutation289.lean)
- [equational_theories/Generated/All4x4Tables/Refutation29.lean](../../equational_theories/Generated/All4x4Tables/Refutation29.lean)
- [equational_theories/Generated/All4x4Tables/Refutation290.lean](../../equational_theories/Generated/All4x4Tables/Refutation290.lean)
- [equational_theories/Generated/All4x4Tables/Refutation291.lean](../../equational_theories/Generated/All4x4Tables/Refutation291.lean)
- [equational_theories/Generated/All4x4Tables/Refutation292.lean](../../equational_theories/Generated/All4x4Tables/Refutation292.lean)
- [equational_theories/Generated/All4x4Tables/Refutation293.lean](../../equational_theories/Generated/All4x4Tables/Refutation293.lean)
- [equational_theories/Generated/All4x4Tables/Refutation294.lean](../../equational_theories/Generated/All4x4Tables/Refutation294.lean)
- [equational_theories/Generated/All4x4Tables/Refutation295.lean](../../equational_theories/Generated/All4x4Tables/Refutation295.lean)
- [equational_theories/Generated/All4x4Tables/Refutation296.lean](../../equational_theories/Generated/All4x4Tables/Refutation296.lean)
- [equational_theories/Generated/All4x4Tables/Refutation297.lean](../../equational_theories/Generated/All4x4Tables/Refutation297.lean)
- [equational_theories/Generated/All4x4Tables/Refutation298.lean](../../equational_theories/Generated/All4x4Tables/Refutation298.lean)
- [equational_theories/Generated/All4x4Tables/Refutation299.lean](../../equational_theories/Generated/All4x4Tables/Refutation299.lean)
- [equational_theories/Generated/All4x4Tables/Refutation3.lean](../../equational_theories/Generated/All4x4Tables/Refutation3.lean)
- [equational_theories/Generated/All4x4Tables/Refutation30.lean](../../equational_theories/Generated/All4x4Tables/Refutation30.lean)
- [equational_theories/Generated/All4x4Tables/Refutation300.lean](../../equational_theories/Generated/All4x4Tables/Refutation300.lean)
- [equational_theories/Generated/All4x4Tables/Refutation301.lean](../../equational_theories/Generated/All4x4Tables/Refutation301.lean)
- [equational_theories/Generated/All4x4Tables/Refutation302.lean](../../equational_theories/Generated/All4x4Tables/Refutation302.lean)
- [equational_theories/Generated/All4x4Tables/Refutation303.lean](../../equational_theories/Generated/All4x4Tables/Refutation303.lean)
- [equational_theories/Generated/All4x4Tables/Refutation304.lean](../../equational_theories/Generated/All4x4Tables/Refutation304.lean)
- [equational_theories/Generated/All4x4Tables/Refutation305.lean](../../equational_theories/Generated/All4x4Tables/Refutation305.lean)
- [equational_theories/Generated/All4x4Tables/Refutation306.lean](../../equational_theories/Generated/All4x4Tables/Refutation306.lean)
- [equational_theories/Generated/All4x4Tables/Refutation307.lean](../../equational_theories/Generated/All4x4Tables/Refutation307.lean)
- [equational_theories/Generated/All4x4Tables/Refutation308.lean](../../equational_theories/Generated/All4x4Tables/Refutation308.lean)
- [equational_theories/Generated/All4x4Tables/Refutation309.lean](../../equational_theories/Generated/All4x4Tables/Refutation309.lean)
- [equational_theories/Generated/All4x4Tables/Refutation31.lean](../../equational_theories/Generated/All4x4Tables/Refutation31.lean)
- [equational_theories/Generated/All4x4Tables/Refutation310.lean](../../equational_theories/Generated/All4x4Tables/Refutation310.lean)
- [equational_theories/Generated/All4x4Tables/Refutation311.lean](../../equational_theories/Generated/All4x4Tables/Refutation311.lean)
- [equational_theories/Generated/All4x4Tables/Refutation312.lean](../../equational_theories/Generated/All4x4Tables/Refutation312.lean)
- [equational_theories/Generated/All4x4Tables/Refutation313.lean](../../equational_theories/Generated/All4x4Tables/Refutation313.lean)
- [equational_theories/Generated/All4x4Tables/Refutation314.lean](../../equational_theories/Generated/All4x4Tables/Refutation314.lean)
- [equational_theories/Generated/All4x4Tables/Refutation315.lean](../../equational_theories/Generated/All4x4Tables/Refutation315.lean)
- [equational_theories/Generated/All4x4Tables/Refutation316.lean](../../equational_theories/Generated/All4x4Tables/Refutation316.lean)
- [equational_theories/Generated/All4x4Tables/Refutation317.lean](../../equational_theories/Generated/All4x4Tables/Refutation317.lean)
- [equational_theories/Generated/All4x4Tables/Refutation318.lean](../../equational_theories/Generated/All4x4Tables/Refutation318.lean)
- [equational_theories/Generated/All4x4Tables/Refutation319.lean](../../equational_theories/Generated/All4x4Tables/Refutation319.lean)
- [equational_theories/Generated/All4x4Tables/Refutation32.lean](../../equational_theories/Generated/All4x4Tables/Refutation32.lean)
- [equational_theories/Generated/All4x4Tables/Refutation320.lean](../../equational_theories/Generated/All4x4Tables/Refutation320.lean)
- [equational_theories/Generated/All4x4Tables/Refutation321.lean](../../equational_theories/Generated/All4x4Tables/Refutation321.lean)
- [equational_theories/Generated/All4x4Tables/Refutation322.lean](../../equational_theories/Generated/All4x4Tables/Refutation322.lean)
- [equational_theories/Generated/All4x4Tables/Refutation323.lean](../../equational_theories/Generated/All4x4Tables/Refutation323.lean)
- [equational_theories/Generated/All4x4Tables/Refutation324.lean](../../equational_theories/Generated/All4x4Tables/Refutation324.lean)
- [equational_theories/Generated/All4x4Tables/Refutation325.lean](../../equational_theories/Generated/All4x4Tables/Refutation325.lean)
- [equational_theories/Generated/All4x4Tables/Refutation326.lean](../../equational_theories/Generated/All4x4Tables/Refutation326.lean)
- [equational_theories/Generated/All4x4Tables/Refutation327.lean](../../equational_theories/Generated/All4x4Tables/Refutation327.lean)
- [equational_theories/Generated/All4x4Tables/Refutation328.lean](../../equational_theories/Generated/All4x4Tables/Refutation328.lean)
- [equational_theories/Generated/All4x4Tables/Refutation329.lean](../../equational_theories/Generated/All4x4Tables/Refutation329.lean)
- [equational_theories/Generated/All4x4Tables/Refutation33.lean](../../equational_theories/Generated/All4x4Tables/Refutation33.lean)
- [equational_theories/Generated/All4x4Tables/Refutation330.lean](../../equational_theories/Generated/All4x4Tables/Refutation330.lean)
- [equational_theories/Generated/All4x4Tables/Refutation331.lean](../../equational_theories/Generated/All4x4Tables/Refutation331.lean)
- [equational_theories/Generated/All4x4Tables/Refutation332.lean](../../equational_theories/Generated/All4x4Tables/Refutation332.lean)
- [equational_theories/Generated/All4x4Tables/Refutation333.lean](../../equational_theories/Generated/All4x4Tables/Refutation333.lean)
- [equational_theories/Generated/All4x4Tables/Refutation334.lean](../../equational_theories/Generated/All4x4Tables/Refutation334.lean)
- [equational_theories/Generated/All4x4Tables/Refutation335.lean](../../equational_theories/Generated/All4x4Tables/Refutation335.lean)
- [equational_theories/Generated/All4x4Tables/Refutation336.lean](../../equational_theories/Generated/All4x4Tables/Refutation336.lean)
- [equational_theories/Generated/All4x4Tables/Refutation337.lean](../../equational_theories/Generated/All4x4Tables/Refutation337.lean)
- [equational_theories/Generated/All4x4Tables/Refutation338.lean](../../equational_theories/Generated/All4x4Tables/Refutation338.lean)
- [equational_theories/Generated/All4x4Tables/Refutation339.lean](../../equational_theories/Generated/All4x4Tables/Refutation339.lean)
- [equational_theories/Generated/All4x4Tables/Refutation34.lean](../../equational_theories/Generated/All4x4Tables/Refutation34.lean)
- [equational_theories/Generated/All4x4Tables/Refutation340.lean](../../equational_theories/Generated/All4x4Tables/Refutation340.lean)
- [equational_theories/Generated/All4x4Tables/Refutation341.lean](../../equational_theories/Generated/All4x4Tables/Refutation341.lean)
- [equational_theories/Generated/All4x4Tables/Refutation342.lean](../../equational_theories/Generated/All4x4Tables/Refutation342.lean)
- [equational_theories/Generated/All4x4Tables/Refutation343.lean](../../equational_theories/Generated/All4x4Tables/Refutation343.lean)
- [equational_theories/Generated/All4x4Tables/Refutation344.lean](../../equational_theories/Generated/All4x4Tables/Refutation344.lean)
- [equational_theories/Generated/All4x4Tables/Refutation345.lean](../../equational_theories/Generated/All4x4Tables/Refutation345.lean)
- [equational_theories/Generated/All4x4Tables/Refutation346.lean](../../equational_theories/Generated/All4x4Tables/Refutation346.lean)
- [equational_theories/Generated/All4x4Tables/Refutation347.lean](../../equational_theories/Generated/All4x4Tables/Refutation347.lean)
- [equational_theories/Generated/All4x4Tables/Refutation348.lean](../../equational_theories/Generated/All4x4Tables/Refutation348.lean)
- [equational_theories/Generated/All4x4Tables/Refutation349.lean](../../equational_theories/Generated/All4x4Tables/Refutation349.lean)
- [equational_theories/Generated/All4x4Tables/Refutation35.lean](../../equational_theories/Generated/All4x4Tables/Refutation35.lean)
- [equational_theories/Generated/All4x4Tables/Refutation350.lean](../../equational_theories/Generated/All4x4Tables/Refutation350.lean)
- [equational_theories/Generated/All4x4Tables/Refutation351.lean](../../equational_theories/Generated/All4x4Tables/Refutation351.lean)
- [equational_theories/Generated/All4x4Tables/Refutation352.lean](../../equational_theories/Generated/All4x4Tables/Refutation352.lean)
- [equational_theories/Generated/All4x4Tables/Refutation353.lean](../../equational_theories/Generated/All4x4Tables/Refutation353.lean)
- [equational_theories/Generated/All4x4Tables/Refutation354.lean](../../equational_theories/Generated/All4x4Tables/Refutation354.lean)
- [equational_theories/Generated/All4x4Tables/Refutation355.lean](../../equational_theories/Generated/All4x4Tables/Refutation355.lean)
- [equational_theories/Generated/All4x4Tables/Refutation356.lean](../../equational_theories/Generated/All4x4Tables/Refutation356.lean)
- [equational_theories/Generated/All4x4Tables/Refutation357.lean](../../equational_theories/Generated/All4x4Tables/Refutation357.lean)
- [equational_theories/Generated/All4x4Tables/Refutation358.lean](../../equational_theories/Generated/All4x4Tables/Refutation358.lean)
- [equational_theories/Generated/All4x4Tables/Refutation359.lean](../../equational_theories/Generated/All4x4Tables/Refutation359.lean)
- [equational_theories/Generated/All4x4Tables/Refutation36.lean](../../equational_theories/Generated/All4x4Tables/Refutation36.lean)
- [equational_theories/Generated/All4x4Tables/Refutation360.lean](../../equational_theories/Generated/All4x4Tables/Refutation360.lean)
- [equational_theories/Generated/All4x4Tables/Refutation361.lean](../../equational_theories/Generated/All4x4Tables/Refutation361.lean)
- [equational_theories/Generated/All4x4Tables/Refutation362.lean](../../equational_theories/Generated/All4x4Tables/Refutation362.lean)
- [equational_theories/Generated/All4x4Tables/Refutation363.lean](../../equational_theories/Generated/All4x4Tables/Refutation363.lean)
- [equational_theories/Generated/All4x4Tables/Refutation364.lean](../../equational_theories/Generated/All4x4Tables/Refutation364.lean)
- [equational_theories/Generated/All4x4Tables/Refutation365.lean](../../equational_theories/Generated/All4x4Tables/Refutation365.lean)
- [equational_theories/Generated/All4x4Tables/Refutation366.lean](../../equational_theories/Generated/All4x4Tables/Refutation366.lean)
- [equational_theories/Generated/All4x4Tables/Refutation367.lean](../../equational_theories/Generated/All4x4Tables/Refutation367.lean)
- [equational_theories/Generated/All4x4Tables/Refutation368.lean](../../equational_theories/Generated/All4x4Tables/Refutation368.lean)
- [equational_theories/Generated/All4x4Tables/Refutation369.lean](../../equational_theories/Generated/All4x4Tables/Refutation369.lean)
- [equational_theories/Generated/All4x4Tables/Refutation37.lean](../../equational_theories/Generated/All4x4Tables/Refutation37.lean)
- [equational_theories/Generated/All4x4Tables/Refutation370.lean](../../equational_theories/Generated/All4x4Tables/Refutation370.lean)
- [equational_theories/Generated/All4x4Tables/Refutation371.lean](../../equational_theories/Generated/All4x4Tables/Refutation371.lean)
- [equational_theories/Generated/All4x4Tables/Refutation372.lean](../../equational_theories/Generated/All4x4Tables/Refutation372.lean)
- [equational_theories/Generated/All4x4Tables/Refutation373.lean](../../equational_theories/Generated/All4x4Tables/Refutation373.lean)
- [equational_theories/Generated/All4x4Tables/Refutation374.lean](../../equational_theories/Generated/All4x4Tables/Refutation374.lean)
- [equational_theories/Generated/All4x4Tables/Refutation375.lean](../../equational_theories/Generated/All4x4Tables/Refutation375.lean)
- [equational_theories/Generated/All4x4Tables/Refutation376.lean](../../equational_theories/Generated/All4x4Tables/Refutation376.lean)
- [equational_theories/Generated/All4x4Tables/Refutation377.lean](../../equational_theories/Generated/All4x4Tables/Refutation377.lean)
- [equational_theories/Generated/All4x4Tables/Refutation378.lean](../../equational_theories/Generated/All4x4Tables/Refutation378.lean)
- [equational_theories/Generated/All4x4Tables/Refutation379.lean](../../equational_theories/Generated/All4x4Tables/Refutation379.lean)
- [equational_theories/Generated/All4x4Tables/Refutation38.lean](../../equational_theories/Generated/All4x4Tables/Refutation38.lean)
- [equational_theories/Generated/All4x4Tables/Refutation380.lean](../../equational_theories/Generated/All4x4Tables/Refutation380.lean)
- [equational_theories/Generated/All4x4Tables/Refutation381.lean](../../equational_theories/Generated/All4x4Tables/Refutation381.lean)
- [equational_theories/Generated/All4x4Tables/Refutation382.lean](../../equational_theories/Generated/All4x4Tables/Refutation382.lean)
- [equational_theories/Generated/All4x4Tables/Refutation383.lean](../../equational_theories/Generated/All4x4Tables/Refutation383.lean)
- [equational_theories/Generated/All4x4Tables/Refutation384.lean](../../equational_theories/Generated/All4x4Tables/Refutation384.lean)
- [equational_theories/Generated/All4x4Tables/Refutation385.lean](../../equational_theories/Generated/All4x4Tables/Refutation385.lean)
- [equational_theories/Generated/All4x4Tables/Refutation386.lean](../../equational_theories/Generated/All4x4Tables/Refutation386.lean)
- [equational_theories/Generated/All4x4Tables/Refutation387.lean](../../equational_theories/Generated/All4x4Tables/Refutation387.lean)
- [equational_theories/Generated/All4x4Tables/Refutation388.lean](../../equational_theories/Generated/All4x4Tables/Refutation388.lean)
- [equational_theories/Generated/All4x4Tables/Refutation389.lean](../../equational_theories/Generated/All4x4Tables/Refutation389.lean)
- [equational_theories/Generated/All4x4Tables/Refutation39.lean](../../equational_theories/Generated/All4x4Tables/Refutation39.lean)
- [equational_theories/Generated/All4x4Tables/Refutation390.lean](../../equational_theories/Generated/All4x4Tables/Refutation390.lean)
- [equational_theories/Generated/All4x4Tables/Refutation391.lean](../../equational_theories/Generated/All4x4Tables/Refutation391.lean)
- [equational_theories/Generated/All4x4Tables/Refutation392.lean](../../equational_theories/Generated/All4x4Tables/Refutation392.lean)
- [equational_theories/Generated/All4x4Tables/Refutation393.lean](../../equational_theories/Generated/All4x4Tables/Refutation393.lean)
- [equational_theories/Generated/All4x4Tables/Refutation394.lean](../../equational_theories/Generated/All4x4Tables/Refutation394.lean)
- [equational_theories/Generated/All4x4Tables/Refutation395.lean](../../equational_theories/Generated/All4x4Tables/Refutation395.lean)
- [equational_theories/Generated/All4x4Tables/Refutation396.lean](../../equational_theories/Generated/All4x4Tables/Refutation396.lean)
- [equational_theories/Generated/All4x4Tables/Refutation397.lean](../../equational_theories/Generated/All4x4Tables/Refutation397.lean)
- [equational_theories/Generated/All4x4Tables/Refutation398.lean](../../equational_theories/Generated/All4x4Tables/Refutation398.lean)
- [equational_theories/Generated/All4x4Tables/Refutation399.lean](../../equational_theories/Generated/All4x4Tables/Refutation399.lean)
- [equational_theories/Generated/All4x4Tables/Refutation4.lean](../../equational_theories/Generated/All4x4Tables/Refutation4.lean)
- [equational_theories/Generated/All4x4Tables/Refutation40.lean](../../equational_theories/Generated/All4x4Tables/Refutation40.lean)
- [equational_theories/Generated/All4x4Tables/Refutation400.lean](../../equational_theories/Generated/All4x4Tables/Refutation400.lean)
- [equational_theories/Generated/All4x4Tables/Refutation401.lean](../../equational_theories/Generated/All4x4Tables/Refutation401.lean)
- [equational_theories/Generated/All4x4Tables/Refutation402.lean](../../equational_theories/Generated/All4x4Tables/Refutation402.lean)
- [equational_theories/Generated/All4x4Tables/Refutation403.lean](../../equational_theories/Generated/All4x4Tables/Refutation403.lean)
- [equational_theories/Generated/All4x4Tables/Refutation404.lean](../../equational_theories/Generated/All4x4Tables/Refutation404.lean)
- [equational_theories/Generated/All4x4Tables/Refutation405.lean](../../equational_theories/Generated/All4x4Tables/Refutation405.lean)
- [equational_theories/Generated/All4x4Tables/Refutation406.lean](../../equational_theories/Generated/All4x4Tables/Refutation406.lean)
- [equational_theories/Generated/All4x4Tables/Refutation407.lean](../../equational_theories/Generated/All4x4Tables/Refutation407.lean)
- [equational_theories/Generated/All4x4Tables/Refutation408.lean](../../equational_theories/Generated/All4x4Tables/Refutation408.lean)
- [equational_theories/Generated/All4x4Tables/Refutation409.lean](../../equational_theories/Generated/All4x4Tables/Refutation409.lean)
- [equational_theories/Generated/All4x4Tables/Refutation41.lean](../../equational_theories/Generated/All4x4Tables/Refutation41.lean)
- [equational_theories/Generated/All4x4Tables/Refutation410.lean](../../equational_theories/Generated/All4x4Tables/Refutation410.lean)
- [equational_theories/Generated/All4x4Tables/Refutation411.lean](../../equational_theories/Generated/All4x4Tables/Refutation411.lean)
- [equational_theories/Generated/All4x4Tables/Refutation412.lean](../../equational_theories/Generated/All4x4Tables/Refutation412.lean)
- [equational_theories/Generated/All4x4Tables/Refutation413.lean](../../equational_theories/Generated/All4x4Tables/Refutation413.lean)
- [equational_theories/Generated/All4x4Tables/Refutation414.lean](../../equational_theories/Generated/All4x4Tables/Refutation414.lean)
- [equational_theories/Generated/All4x4Tables/Refutation415.lean](../../equational_theories/Generated/All4x4Tables/Refutation415.lean)
- [equational_theories/Generated/All4x4Tables/Refutation416.lean](../../equational_theories/Generated/All4x4Tables/Refutation416.lean)
- [equational_theories/Generated/All4x4Tables/Refutation417.lean](../../equational_theories/Generated/All4x4Tables/Refutation417.lean)
- [equational_theories/Generated/All4x4Tables/Refutation418.lean](../../equational_theories/Generated/All4x4Tables/Refutation418.lean)
- [equational_theories/Generated/All4x4Tables/Refutation419.lean](../../equational_theories/Generated/All4x4Tables/Refutation419.lean)
- [equational_theories/Generated/All4x4Tables/Refutation42.lean](../../equational_theories/Generated/All4x4Tables/Refutation42.lean)
- [equational_theories/Generated/All4x4Tables/Refutation420.lean](../../equational_theories/Generated/All4x4Tables/Refutation420.lean)
- [equational_theories/Generated/All4x4Tables/Refutation421.lean](../../equational_theories/Generated/All4x4Tables/Refutation421.lean)
- [equational_theories/Generated/All4x4Tables/Refutation422.lean](../../equational_theories/Generated/All4x4Tables/Refutation422.lean)
- [equational_theories/Generated/All4x4Tables/Refutation423.lean](../../equational_theories/Generated/All4x4Tables/Refutation423.lean)
- [equational_theories/Generated/All4x4Tables/Refutation424.lean](../../equational_theories/Generated/All4x4Tables/Refutation424.lean)
- [equational_theories/Generated/All4x4Tables/Refutation425.lean](../../equational_theories/Generated/All4x4Tables/Refutation425.lean)
- [equational_theories/Generated/All4x4Tables/Refutation426.lean](../../equational_theories/Generated/All4x4Tables/Refutation426.lean)
- [equational_theories/Generated/All4x4Tables/Refutation427.lean](../../equational_theories/Generated/All4x4Tables/Refutation427.lean)
- [equational_theories/Generated/All4x4Tables/Refutation428.lean](../../equational_theories/Generated/All4x4Tables/Refutation428.lean)
- [equational_theories/Generated/All4x4Tables/Refutation429.lean](../../equational_theories/Generated/All4x4Tables/Refutation429.lean)
- [equational_theories/Generated/All4x4Tables/Refutation43.lean](../../equational_theories/Generated/All4x4Tables/Refutation43.lean)
- [equational_theories/Generated/All4x4Tables/Refutation430.lean](../../equational_theories/Generated/All4x4Tables/Refutation430.lean)
- [equational_theories/Generated/All4x4Tables/Refutation431.lean](../../equational_theories/Generated/All4x4Tables/Refutation431.lean)
- [equational_theories/Generated/All4x4Tables/Refutation432.lean](../../equational_theories/Generated/All4x4Tables/Refutation432.lean)
- [equational_theories/Generated/All4x4Tables/Refutation433.lean](../../equational_theories/Generated/All4x4Tables/Refutation433.lean)
- [equational_theories/Generated/All4x4Tables/Refutation434.lean](../../equational_theories/Generated/All4x4Tables/Refutation434.lean)
- [equational_theories/Generated/All4x4Tables/Refutation435.lean](../../equational_theories/Generated/All4x4Tables/Refutation435.lean)
- [equational_theories/Generated/All4x4Tables/Refutation436.lean](../../equational_theories/Generated/All4x4Tables/Refutation436.lean)
- [equational_theories/Generated/All4x4Tables/Refutation437.lean](../../equational_theories/Generated/All4x4Tables/Refutation437.lean)
- [equational_theories/Generated/All4x4Tables/Refutation438.lean](../../equational_theories/Generated/All4x4Tables/Refutation438.lean)
- [equational_theories/Generated/All4x4Tables/Refutation439.lean](../../equational_theories/Generated/All4x4Tables/Refutation439.lean)
- [equational_theories/Generated/All4x4Tables/Refutation44.lean](../../equational_theories/Generated/All4x4Tables/Refutation44.lean)
- [equational_theories/Generated/All4x4Tables/Refutation440.lean](../../equational_theories/Generated/All4x4Tables/Refutation440.lean)
- [equational_theories/Generated/All4x4Tables/Refutation441.lean](../../equational_theories/Generated/All4x4Tables/Refutation441.lean)
- [equational_theories/Generated/All4x4Tables/Refutation442.lean](../../equational_theories/Generated/All4x4Tables/Refutation442.lean)
- [equational_theories/Generated/All4x4Tables/Refutation443.lean](../../equational_theories/Generated/All4x4Tables/Refutation443.lean)
- [equational_theories/Generated/All4x4Tables/Refutation444.lean](../../equational_theories/Generated/All4x4Tables/Refutation444.lean)
- [equational_theories/Generated/All4x4Tables/Refutation445.lean](../../equational_theories/Generated/All4x4Tables/Refutation445.lean)
- [equational_theories/Generated/All4x4Tables/Refutation446.lean](../../equational_theories/Generated/All4x4Tables/Refutation446.lean)
- [equational_theories/Generated/All4x4Tables/Refutation447.lean](../../equational_theories/Generated/All4x4Tables/Refutation447.lean)
- [equational_theories/Generated/All4x4Tables/Refutation448.lean](../../equational_theories/Generated/All4x4Tables/Refutation448.lean)
- [equational_theories/Generated/All4x4Tables/Refutation449.lean](../../equational_theories/Generated/All4x4Tables/Refutation449.lean)
- [equational_theories/Generated/All4x4Tables/Refutation45.lean](../../equational_theories/Generated/All4x4Tables/Refutation45.lean)
- [equational_theories/Generated/All4x4Tables/Refutation450.lean](../../equational_theories/Generated/All4x4Tables/Refutation450.lean)
- [equational_theories/Generated/All4x4Tables/Refutation451.lean](../../equational_theories/Generated/All4x4Tables/Refutation451.lean)
- [equational_theories/Generated/All4x4Tables/Refutation452.lean](../../equational_theories/Generated/All4x4Tables/Refutation452.lean)
- [equational_theories/Generated/All4x4Tables/Refutation453.lean](../../equational_theories/Generated/All4x4Tables/Refutation453.lean)
- [equational_theories/Generated/All4x4Tables/Refutation454.lean](../../equational_theories/Generated/All4x4Tables/Refutation454.lean)
- [equational_theories/Generated/All4x4Tables/Refutation455.lean](../../equational_theories/Generated/All4x4Tables/Refutation455.lean)
- [equational_theories/Generated/All4x4Tables/Refutation456.lean](../../equational_theories/Generated/All4x4Tables/Refutation456.lean)
- [equational_theories/Generated/All4x4Tables/Refutation457.lean](../../equational_theories/Generated/All4x4Tables/Refutation457.lean)
- [equational_theories/Generated/All4x4Tables/Refutation458.lean](../../equational_theories/Generated/All4x4Tables/Refutation458.lean)
- [equational_theories/Generated/All4x4Tables/Refutation459.lean](../../equational_theories/Generated/All4x4Tables/Refutation459.lean)
- [equational_theories/Generated/All4x4Tables/Refutation46.lean](../../equational_theories/Generated/All4x4Tables/Refutation46.lean)
- [equational_theories/Generated/All4x4Tables/Refutation460.lean](../../equational_theories/Generated/All4x4Tables/Refutation460.lean)
- [equational_theories/Generated/All4x4Tables/Refutation461.lean](../../equational_theories/Generated/All4x4Tables/Refutation461.lean)
- [equational_theories/Generated/All4x4Tables/Refutation462.lean](../../equational_theories/Generated/All4x4Tables/Refutation462.lean)
- [equational_theories/Generated/All4x4Tables/Refutation463.lean](../../equational_theories/Generated/All4x4Tables/Refutation463.lean)
- [equational_theories/Generated/All4x4Tables/Refutation464.lean](../../equational_theories/Generated/All4x4Tables/Refutation464.lean)
- [equational_theories/Generated/All4x4Tables/Refutation465.lean](../../equational_theories/Generated/All4x4Tables/Refutation465.lean)
- [equational_theories/Generated/All4x4Tables/Refutation466.lean](../../equational_theories/Generated/All4x4Tables/Refutation466.lean)
- [equational_theories/Generated/All4x4Tables/Refutation467.lean](../../equational_theories/Generated/All4x4Tables/Refutation467.lean)
- [equational_theories/Generated/All4x4Tables/Refutation468.lean](../../equational_theories/Generated/All4x4Tables/Refutation468.lean)
- [equational_theories/Generated/All4x4Tables/Refutation469.lean](../../equational_theories/Generated/All4x4Tables/Refutation469.lean)
- [equational_theories/Generated/All4x4Tables/Refutation47.lean](../../equational_theories/Generated/All4x4Tables/Refutation47.lean)
- [equational_theories/Generated/All4x4Tables/Refutation470.lean](../../equational_theories/Generated/All4x4Tables/Refutation470.lean)
- [equational_theories/Generated/All4x4Tables/Refutation471.lean](../../equational_theories/Generated/All4x4Tables/Refutation471.lean)
- [equational_theories/Generated/All4x4Tables/Refutation472.lean](../../equational_theories/Generated/All4x4Tables/Refutation472.lean)
- [equational_theories/Generated/All4x4Tables/Refutation473.lean](../../equational_theories/Generated/All4x4Tables/Refutation473.lean)
- [equational_theories/Generated/All4x4Tables/Refutation474.lean](../../equational_theories/Generated/All4x4Tables/Refutation474.lean)
- [equational_theories/Generated/All4x4Tables/Refutation475.lean](../../equational_theories/Generated/All4x4Tables/Refutation475.lean)
- [equational_theories/Generated/All4x4Tables/Refutation476.lean](../../equational_theories/Generated/All4x4Tables/Refutation476.lean)
- [equational_theories/Generated/All4x4Tables/Refutation477.lean](../../equational_theories/Generated/All4x4Tables/Refutation477.lean)
- [equational_theories/Generated/All4x4Tables/Refutation478.lean](../../equational_theories/Generated/All4x4Tables/Refutation478.lean)
- [equational_theories/Generated/All4x4Tables/Refutation479.lean](../../equational_theories/Generated/All4x4Tables/Refutation479.lean)
- [equational_theories/Generated/All4x4Tables/Refutation48.lean](../../equational_theories/Generated/All4x4Tables/Refutation48.lean)
- [equational_theories/Generated/All4x4Tables/Refutation480.lean](../../equational_theories/Generated/All4x4Tables/Refutation480.lean)
- [equational_theories/Generated/All4x4Tables/Refutation481.lean](../../equational_theories/Generated/All4x4Tables/Refutation481.lean)
- [equational_theories/Generated/All4x4Tables/Refutation482.lean](../../equational_theories/Generated/All4x4Tables/Refutation482.lean)
- [equational_theories/Generated/All4x4Tables/Refutation483.lean](../../equational_theories/Generated/All4x4Tables/Refutation483.lean)
- [equational_theories/Generated/All4x4Tables/Refutation484.lean](../../equational_theories/Generated/All4x4Tables/Refutation484.lean)
- [equational_theories/Generated/All4x4Tables/Refutation485.lean](../../equational_theories/Generated/All4x4Tables/Refutation485.lean)
- [equational_theories/Generated/All4x4Tables/Refutation486.lean](../../equational_theories/Generated/All4x4Tables/Refutation486.lean)
- [equational_theories/Generated/All4x4Tables/Refutation487.lean](../../equational_theories/Generated/All4x4Tables/Refutation487.lean)
- [equational_theories/Generated/All4x4Tables/Refutation488.lean](../../equational_theories/Generated/All4x4Tables/Refutation488.lean)
- [equational_theories/Generated/All4x4Tables/Refutation489.lean](../../equational_theories/Generated/All4x4Tables/Refutation489.lean)
- [equational_theories/Generated/All4x4Tables/Refutation49.lean](../../equational_theories/Generated/All4x4Tables/Refutation49.lean)
- [equational_theories/Generated/All4x4Tables/Refutation490.lean](../../equational_theories/Generated/All4x4Tables/Refutation490.lean)
- [equational_theories/Generated/All4x4Tables/Refutation491.lean](../../equational_theories/Generated/All4x4Tables/Refutation491.lean)
- [equational_theories/Generated/All4x4Tables/Refutation492.lean](../../equational_theories/Generated/All4x4Tables/Refutation492.lean)
- [equational_theories/Generated/All4x4Tables/Refutation493.lean](../../equational_theories/Generated/All4x4Tables/Refutation493.lean)
- [equational_theories/Generated/All4x4Tables/Refutation494.lean](../../equational_theories/Generated/All4x4Tables/Refutation494.lean)
- [equational_theories/Generated/All4x4Tables/Refutation495.lean](../../equational_theories/Generated/All4x4Tables/Refutation495.lean)
- [equational_theories/Generated/All4x4Tables/Refutation496.lean](../../equational_theories/Generated/All4x4Tables/Refutation496.lean)
- [equational_theories/Generated/All4x4Tables/Refutation497.lean](../../equational_theories/Generated/All4x4Tables/Refutation497.lean)
- [equational_theories/Generated/All4x4Tables/Refutation498.lean](../../equational_theories/Generated/All4x4Tables/Refutation498.lean)
- [equational_theories/Generated/All4x4Tables/Refutation499.lean](../../equational_theories/Generated/All4x4Tables/Refutation499.lean)
- [equational_theories/Generated/All4x4Tables/Refutation5.lean](../../equational_theories/Generated/All4x4Tables/Refutation5.lean)
- [equational_theories/Generated/All4x4Tables/Refutation50.lean](../../equational_theories/Generated/All4x4Tables/Refutation50.lean)
- [equational_theories/Generated/All4x4Tables/Refutation500.lean](../../equational_theories/Generated/All4x4Tables/Refutation500.lean)
- [equational_theories/Generated/All4x4Tables/Refutation501.lean](../../equational_theories/Generated/All4x4Tables/Refutation501.lean)
- [equational_theories/Generated/All4x4Tables/Refutation502.lean](../../equational_theories/Generated/All4x4Tables/Refutation502.lean)
- [equational_theories/Generated/All4x4Tables/Refutation503.lean](../../equational_theories/Generated/All4x4Tables/Refutation503.lean)
- [equational_theories/Generated/All4x4Tables/Refutation504.lean](../../equational_theories/Generated/All4x4Tables/Refutation504.lean)
- [equational_theories/Generated/All4x4Tables/Refutation505.lean](../../equational_theories/Generated/All4x4Tables/Refutation505.lean)
- [equational_theories/Generated/All4x4Tables/Refutation506.lean](../../equational_theories/Generated/All4x4Tables/Refutation506.lean)
- [equational_theories/Generated/All4x4Tables/Refutation507.lean](../../equational_theories/Generated/All4x4Tables/Refutation507.lean)
- [equational_theories/Generated/All4x4Tables/Refutation508.lean](../../equational_theories/Generated/All4x4Tables/Refutation508.lean)
- [equational_theories/Generated/All4x4Tables/Refutation509.lean](../../equational_theories/Generated/All4x4Tables/Refutation509.lean)
- [equational_theories/Generated/All4x4Tables/Refutation51.lean](../../equational_theories/Generated/All4x4Tables/Refutation51.lean)
- [equational_theories/Generated/All4x4Tables/Refutation510.lean](../../equational_theories/Generated/All4x4Tables/Refutation510.lean)
- [equational_theories/Generated/All4x4Tables/Refutation511.lean](../../equational_theories/Generated/All4x4Tables/Refutation511.lean)
- [equational_theories/Generated/All4x4Tables/Refutation512.lean](../../equational_theories/Generated/All4x4Tables/Refutation512.lean)
- [equational_theories/Generated/All4x4Tables/Refutation513.lean](../../equational_theories/Generated/All4x4Tables/Refutation513.lean)
- [equational_theories/Generated/All4x4Tables/Refutation514.lean](../../equational_theories/Generated/All4x4Tables/Refutation514.lean)
- [equational_theories/Generated/All4x4Tables/Refutation515.lean](../../equational_theories/Generated/All4x4Tables/Refutation515.lean)
- [equational_theories/Generated/All4x4Tables/Refutation516.lean](../../equational_theories/Generated/All4x4Tables/Refutation516.lean)
- [equational_theories/Generated/All4x4Tables/Refutation517.lean](../../equational_theories/Generated/All4x4Tables/Refutation517.lean)
- [equational_theories/Generated/All4x4Tables/Refutation518.lean](../../equational_theories/Generated/All4x4Tables/Refutation518.lean)
- [equational_theories/Generated/All4x4Tables/Refutation519.lean](../../equational_theories/Generated/All4x4Tables/Refutation519.lean)
- [equational_theories/Generated/All4x4Tables/Refutation52.lean](../../equational_theories/Generated/All4x4Tables/Refutation52.lean)
- [equational_theories/Generated/All4x4Tables/Refutation520.lean](../../equational_theories/Generated/All4x4Tables/Refutation520.lean)
- [equational_theories/Generated/All4x4Tables/Refutation521.lean](../../equational_theories/Generated/All4x4Tables/Refutation521.lean)
- [equational_theories/Generated/All4x4Tables/Refutation522.lean](../../equational_theories/Generated/All4x4Tables/Refutation522.lean)
- [equational_theories/Generated/All4x4Tables/Refutation523.lean](../../equational_theories/Generated/All4x4Tables/Refutation523.lean)
- [equational_theories/Generated/All4x4Tables/Refutation524.lean](../../equational_theories/Generated/All4x4Tables/Refutation524.lean)
- [equational_theories/Generated/All4x4Tables/Refutation525.lean](../../equational_theories/Generated/All4x4Tables/Refutation525.lean)
- [equational_theories/Generated/All4x4Tables/Refutation526.lean](../../equational_theories/Generated/All4x4Tables/Refutation526.lean)
- [equational_theories/Generated/All4x4Tables/Refutation527.lean](../../equational_theories/Generated/All4x4Tables/Refutation527.lean)
- [equational_theories/Generated/All4x4Tables/Refutation528.lean](../../equational_theories/Generated/All4x4Tables/Refutation528.lean)
- [equational_theories/Generated/All4x4Tables/Refutation529.lean](../../equational_theories/Generated/All4x4Tables/Refutation529.lean)
- [equational_theories/Generated/All4x4Tables/Refutation53.lean](../../equational_theories/Generated/All4x4Tables/Refutation53.lean)
- [equational_theories/Generated/All4x4Tables/Refutation530.lean](../../equational_theories/Generated/All4x4Tables/Refutation530.lean)
- [equational_theories/Generated/All4x4Tables/Refutation531.lean](../../equational_theories/Generated/All4x4Tables/Refutation531.lean)
- [equational_theories/Generated/All4x4Tables/Refutation532.lean](../../equational_theories/Generated/All4x4Tables/Refutation532.lean)
- [equational_theories/Generated/All4x4Tables/Refutation533.lean](../../equational_theories/Generated/All4x4Tables/Refutation533.lean)
- [equational_theories/Generated/All4x4Tables/Refutation534.lean](../../equational_theories/Generated/All4x4Tables/Refutation534.lean)
- [equational_theories/Generated/All4x4Tables/Refutation535.lean](../../equational_theories/Generated/All4x4Tables/Refutation535.lean)
- [equational_theories/Generated/All4x4Tables/Refutation536.lean](../../equational_theories/Generated/All4x4Tables/Refutation536.lean)
- [equational_theories/Generated/All4x4Tables/Refutation537.lean](../../equational_theories/Generated/All4x4Tables/Refutation537.lean)
- [equational_theories/Generated/All4x4Tables/Refutation538.lean](../../equational_theories/Generated/All4x4Tables/Refutation538.lean)
- [equational_theories/Generated/All4x4Tables/Refutation539.lean](../../equational_theories/Generated/All4x4Tables/Refutation539.lean)
- [equational_theories/Generated/All4x4Tables/Refutation54.lean](../../equational_theories/Generated/All4x4Tables/Refutation54.lean)
- [equational_theories/Generated/All4x4Tables/Refutation540.lean](../../equational_theories/Generated/All4x4Tables/Refutation540.lean)
- [equational_theories/Generated/All4x4Tables/Refutation541.lean](../../equational_theories/Generated/All4x4Tables/Refutation541.lean)
- [equational_theories/Generated/All4x4Tables/Refutation542.lean](../../equational_theories/Generated/All4x4Tables/Refutation542.lean)
- [equational_theories/Generated/All4x4Tables/Refutation543.lean](../../equational_theories/Generated/All4x4Tables/Refutation543.lean)
- [equational_theories/Generated/All4x4Tables/Refutation544.lean](../../equational_theories/Generated/All4x4Tables/Refutation544.lean)
- [equational_theories/Generated/All4x4Tables/Refutation545.lean](../../equational_theories/Generated/All4x4Tables/Refutation545.lean)
- [equational_theories/Generated/All4x4Tables/Refutation546.lean](../../equational_theories/Generated/All4x4Tables/Refutation546.lean)
- [equational_theories/Generated/All4x4Tables/Refutation547.lean](../../equational_theories/Generated/All4x4Tables/Refutation547.lean)
- [equational_theories/Generated/All4x4Tables/Refutation548.lean](../../equational_theories/Generated/All4x4Tables/Refutation548.lean)
- [equational_theories/Generated/All4x4Tables/Refutation549.lean](../../equational_theories/Generated/All4x4Tables/Refutation549.lean)
- [equational_theories/Generated/All4x4Tables/Refutation55.lean](../../equational_theories/Generated/All4x4Tables/Refutation55.lean)
- [equational_theories/Generated/All4x4Tables/Refutation550.lean](../../equational_theories/Generated/All4x4Tables/Refutation550.lean)
- [equational_theories/Generated/All4x4Tables/Refutation551.lean](../../equational_theories/Generated/All4x4Tables/Refutation551.lean)
- [equational_theories/Generated/All4x4Tables/Refutation552.lean](../../equational_theories/Generated/All4x4Tables/Refutation552.lean)
- [equational_theories/Generated/All4x4Tables/Refutation553.lean](../../equational_theories/Generated/All4x4Tables/Refutation553.lean)
- [equational_theories/Generated/All4x4Tables/Refutation554.lean](../../equational_theories/Generated/All4x4Tables/Refutation554.lean)
- [equational_theories/Generated/All4x4Tables/Refutation555.lean](../../equational_theories/Generated/All4x4Tables/Refutation555.lean)
- [equational_theories/Generated/All4x4Tables/Refutation556.lean](../../equational_theories/Generated/All4x4Tables/Refutation556.lean)
- [equational_theories/Generated/All4x4Tables/Refutation557.lean](../../equational_theories/Generated/All4x4Tables/Refutation557.lean)
- [equational_theories/Generated/All4x4Tables/Refutation558.lean](../../equational_theories/Generated/All4x4Tables/Refutation558.lean)
- [equational_theories/Generated/All4x4Tables/Refutation559.lean](../../equational_theories/Generated/All4x4Tables/Refutation559.lean)
- [equational_theories/Generated/All4x4Tables/Refutation56.lean](../../equational_theories/Generated/All4x4Tables/Refutation56.lean)
- [equational_theories/Generated/All4x4Tables/Refutation560.lean](../../equational_theories/Generated/All4x4Tables/Refutation560.lean)
- [equational_theories/Generated/All4x4Tables/Refutation561.lean](../../equational_theories/Generated/All4x4Tables/Refutation561.lean)
- [equational_theories/Generated/All4x4Tables/Refutation562.lean](../../equational_theories/Generated/All4x4Tables/Refutation562.lean)
- [equational_theories/Generated/All4x4Tables/Refutation563.lean](../../equational_theories/Generated/All4x4Tables/Refutation563.lean)
- [equational_theories/Generated/All4x4Tables/Refutation564.lean](../../equational_theories/Generated/All4x4Tables/Refutation564.lean)
- [equational_theories/Generated/All4x4Tables/Refutation565.lean](../../equational_theories/Generated/All4x4Tables/Refutation565.lean)
- [equational_theories/Generated/All4x4Tables/Refutation566.lean](../../equational_theories/Generated/All4x4Tables/Refutation566.lean)
- [equational_theories/Generated/All4x4Tables/Refutation567.lean](../../equational_theories/Generated/All4x4Tables/Refutation567.lean)
- [equational_theories/Generated/All4x4Tables/Refutation568.lean](../../equational_theories/Generated/All4x4Tables/Refutation568.lean)
- [equational_theories/Generated/All4x4Tables/Refutation569.lean](../../equational_theories/Generated/All4x4Tables/Refutation569.lean)
- [equational_theories/Generated/All4x4Tables/Refutation57.lean](../../equational_theories/Generated/All4x4Tables/Refutation57.lean)
- [equational_theories/Generated/All4x4Tables/Refutation570.lean](../../equational_theories/Generated/All4x4Tables/Refutation570.lean)
- [equational_theories/Generated/All4x4Tables/Refutation571.lean](../../equational_theories/Generated/All4x4Tables/Refutation571.lean)
- [equational_theories/Generated/All4x4Tables/Refutation572.lean](../../equational_theories/Generated/All4x4Tables/Refutation572.lean)
- [equational_theories/Generated/All4x4Tables/Refutation573.lean](../../equational_theories/Generated/All4x4Tables/Refutation573.lean)
- [equational_theories/Generated/All4x4Tables/Refutation574.lean](../../equational_theories/Generated/All4x4Tables/Refutation574.lean)
- [equational_theories/Generated/All4x4Tables/Refutation575.lean](../../equational_theories/Generated/All4x4Tables/Refutation575.lean)
- [equational_theories/Generated/All4x4Tables/Refutation576.lean](../../equational_theories/Generated/All4x4Tables/Refutation576.lean)
- [equational_theories/Generated/All4x4Tables/Refutation577.lean](../../equational_theories/Generated/All4x4Tables/Refutation577.lean)
- [equational_theories/Generated/All4x4Tables/Refutation578.lean](../../equational_theories/Generated/All4x4Tables/Refutation578.lean)
- [equational_theories/Generated/All4x4Tables/Refutation579.lean](../../equational_theories/Generated/All4x4Tables/Refutation579.lean)
- [equational_theories/Generated/All4x4Tables/Refutation58.lean](../../equational_theories/Generated/All4x4Tables/Refutation58.lean)
- [equational_theories/Generated/All4x4Tables/Refutation580.lean](../../equational_theories/Generated/All4x4Tables/Refutation580.lean)
- [equational_theories/Generated/All4x4Tables/Refutation581.lean](../../equational_theories/Generated/All4x4Tables/Refutation581.lean)
- [equational_theories/Generated/All4x4Tables/Refutation582.lean](../../equational_theories/Generated/All4x4Tables/Refutation582.lean)
- [equational_theories/Generated/All4x4Tables/Refutation583.lean](../../equational_theories/Generated/All4x4Tables/Refutation583.lean)
- [equational_theories/Generated/All4x4Tables/Refutation584.lean](../../equational_theories/Generated/All4x4Tables/Refutation584.lean)
- [equational_theories/Generated/All4x4Tables/Refutation585.lean](../../equational_theories/Generated/All4x4Tables/Refutation585.lean)
- [equational_theories/Generated/All4x4Tables/Refutation586.lean](../../equational_theories/Generated/All4x4Tables/Refutation586.lean)
- [equational_theories/Generated/All4x4Tables/Refutation587.lean](../../equational_theories/Generated/All4x4Tables/Refutation587.lean)
- [equational_theories/Generated/All4x4Tables/Refutation588.lean](../../equational_theories/Generated/All4x4Tables/Refutation588.lean)
- [equational_theories/Generated/All4x4Tables/Refutation589.lean](../../equational_theories/Generated/All4x4Tables/Refutation589.lean)
- [equational_theories/Generated/All4x4Tables/Refutation59.lean](../../equational_theories/Generated/All4x4Tables/Refutation59.lean)
- [equational_theories/Generated/All4x4Tables/Refutation590.lean](../../equational_theories/Generated/All4x4Tables/Refutation590.lean)
- [equational_theories/Generated/All4x4Tables/Refutation591.lean](../../equational_theories/Generated/All4x4Tables/Refutation591.lean)
- [equational_theories/Generated/All4x4Tables/Refutation592.lean](../../equational_theories/Generated/All4x4Tables/Refutation592.lean)
- [equational_theories/Generated/All4x4Tables/Refutation593.lean](../../equational_theories/Generated/All4x4Tables/Refutation593.lean)
- [equational_theories/Generated/All4x4Tables/Refutation594.lean](../../equational_theories/Generated/All4x4Tables/Refutation594.lean)
- [equational_theories/Generated/All4x4Tables/Refutation595.lean](../../equational_theories/Generated/All4x4Tables/Refutation595.lean)
- [equational_theories/Generated/All4x4Tables/Refutation596.lean](../../equational_theories/Generated/All4x4Tables/Refutation596.lean)
- [equational_theories/Generated/All4x4Tables/Refutation597.lean](../../equational_theories/Generated/All4x4Tables/Refutation597.lean)
- [equational_theories/Generated/All4x4Tables/Refutation598.lean](../../equational_theories/Generated/All4x4Tables/Refutation598.lean)
- [equational_theories/Generated/All4x4Tables/Refutation599.lean](../../equational_theories/Generated/All4x4Tables/Refutation599.lean)
- [equational_theories/Generated/All4x4Tables/Refutation6.lean](../../equational_theories/Generated/All4x4Tables/Refutation6.lean)
- [equational_theories/Generated/All4x4Tables/Refutation60.lean](../../equational_theories/Generated/All4x4Tables/Refutation60.lean)
- [equational_theories/Generated/All4x4Tables/Refutation600.lean](../../equational_theories/Generated/All4x4Tables/Refutation600.lean)
- [equational_theories/Generated/All4x4Tables/Refutation601.lean](../../equational_theories/Generated/All4x4Tables/Refutation601.lean)
- [equational_theories/Generated/All4x4Tables/Refutation602.lean](../../equational_theories/Generated/All4x4Tables/Refutation602.lean)
- [equational_theories/Generated/All4x4Tables/Refutation603.lean](../../equational_theories/Generated/All4x4Tables/Refutation603.lean)
- [equational_theories/Generated/All4x4Tables/Refutation604.lean](../../equational_theories/Generated/All4x4Tables/Refutation604.lean)
- [equational_theories/Generated/All4x4Tables/Refutation605.lean](../../equational_theories/Generated/All4x4Tables/Refutation605.lean)
- [equational_theories/Generated/All4x4Tables/Refutation606.lean](../../equational_theories/Generated/All4x4Tables/Refutation606.lean)
- [equational_theories/Generated/All4x4Tables/Refutation607.lean](../../equational_theories/Generated/All4x4Tables/Refutation607.lean)
- [equational_theories/Generated/All4x4Tables/Refutation608.lean](../../equational_theories/Generated/All4x4Tables/Refutation608.lean)
- [equational_theories/Generated/All4x4Tables/Refutation609.lean](../../equational_theories/Generated/All4x4Tables/Refutation609.lean)
- [equational_theories/Generated/All4x4Tables/Refutation61.lean](../../equational_theories/Generated/All4x4Tables/Refutation61.lean)
- [equational_theories/Generated/All4x4Tables/Refutation610.lean](../../equational_theories/Generated/All4x4Tables/Refutation610.lean)
- [equational_theories/Generated/All4x4Tables/Refutation611.lean](../../equational_theories/Generated/All4x4Tables/Refutation611.lean)
- [equational_theories/Generated/All4x4Tables/Refutation612.lean](../../equational_theories/Generated/All4x4Tables/Refutation612.lean)
- [equational_theories/Generated/All4x4Tables/Refutation613.lean](../../equational_theories/Generated/All4x4Tables/Refutation613.lean)
- [equational_theories/Generated/All4x4Tables/Refutation614.lean](../../equational_theories/Generated/All4x4Tables/Refutation614.lean)
- [equational_theories/Generated/All4x4Tables/Refutation615.lean](../../equational_theories/Generated/All4x4Tables/Refutation615.lean)
- [equational_theories/Generated/All4x4Tables/Refutation616.lean](../../equational_theories/Generated/All4x4Tables/Refutation616.lean)
- [equational_theories/Generated/All4x4Tables/Refutation617.lean](../../equational_theories/Generated/All4x4Tables/Refutation617.lean)
- [equational_theories/Generated/All4x4Tables/Refutation618.lean](../../equational_theories/Generated/All4x4Tables/Refutation618.lean)
- [equational_theories/Generated/All4x4Tables/Refutation619.lean](../../equational_theories/Generated/All4x4Tables/Refutation619.lean)
- [equational_theories/Generated/All4x4Tables/Refutation62.lean](../../equational_theories/Generated/All4x4Tables/Refutation62.lean)
- [equational_theories/Generated/All4x4Tables/Refutation620.lean](../../equational_theories/Generated/All4x4Tables/Refutation620.lean)
- [equational_theories/Generated/All4x4Tables/Refutation621.lean](../../equational_theories/Generated/All4x4Tables/Refutation621.lean)
- [equational_theories/Generated/All4x4Tables/Refutation622.lean](../../equational_theories/Generated/All4x4Tables/Refutation622.lean)
- [equational_theories/Generated/All4x4Tables/Refutation623.lean](../../equational_theories/Generated/All4x4Tables/Refutation623.lean)
- [equational_theories/Generated/All4x4Tables/Refutation624.lean](../../equational_theories/Generated/All4x4Tables/Refutation624.lean)
- [equational_theories/Generated/All4x4Tables/Refutation625.lean](../../equational_theories/Generated/All4x4Tables/Refutation625.lean)
- [equational_theories/Generated/All4x4Tables/Refutation626.lean](../../equational_theories/Generated/All4x4Tables/Refutation626.lean)
- [equational_theories/Generated/All4x4Tables/Refutation627.lean](../../equational_theories/Generated/All4x4Tables/Refutation627.lean)
- [equational_theories/Generated/All4x4Tables/Refutation628.lean](../../equational_theories/Generated/All4x4Tables/Refutation628.lean)
- [equational_theories/Generated/All4x4Tables/Refutation629.lean](../../equational_theories/Generated/All4x4Tables/Refutation629.lean)
- [equational_theories/Generated/All4x4Tables/Refutation63.lean](../../equational_theories/Generated/All4x4Tables/Refutation63.lean)
- [equational_theories/Generated/All4x4Tables/Refutation630.lean](../../equational_theories/Generated/All4x4Tables/Refutation630.lean)
- [equational_theories/Generated/All4x4Tables/Refutation631.lean](../../equational_theories/Generated/All4x4Tables/Refutation631.lean)
- [equational_theories/Generated/All4x4Tables/Refutation632.lean](../../equational_theories/Generated/All4x4Tables/Refutation632.lean)
- [equational_theories/Generated/All4x4Tables/Refutation633.lean](../../equational_theories/Generated/All4x4Tables/Refutation633.lean)
- [equational_theories/Generated/All4x4Tables/Refutation634.lean](../../equational_theories/Generated/All4x4Tables/Refutation634.lean)
- [equational_theories/Generated/All4x4Tables/Refutation635.lean](../../equational_theories/Generated/All4x4Tables/Refutation635.lean)
- [equational_theories/Generated/All4x4Tables/Refutation636.lean](../../equational_theories/Generated/All4x4Tables/Refutation636.lean)
- [equational_theories/Generated/All4x4Tables/Refutation637.lean](../../equational_theories/Generated/All4x4Tables/Refutation637.lean)
- [equational_theories/Generated/All4x4Tables/Refutation638.lean](../../equational_theories/Generated/All4x4Tables/Refutation638.lean)
- [equational_theories/Generated/All4x4Tables/Refutation639.lean](../../equational_theories/Generated/All4x4Tables/Refutation639.lean)
- [equational_theories/Generated/All4x4Tables/Refutation64.lean](../../equational_theories/Generated/All4x4Tables/Refutation64.lean)
- [equational_theories/Generated/All4x4Tables/Refutation640.lean](../../equational_theories/Generated/All4x4Tables/Refutation640.lean)
- [equational_theories/Generated/All4x4Tables/Refutation641.lean](../../equational_theories/Generated/All4x4Tables/Refutation641.lean)
- [equational_theories/Generated/All4x4Tables/Refutation642.lean](../../equational_theories/Generated/All4x4Tables/Refutation642.lean)
- [equational_theories/Generated/All4x4Tables/Refutation643.lean](../../equational_theories/Generated/All4x4Tables/Refutation643.lean)
- [equational_theories/Generated/All4x4Tables/Refutation644.lean](../../equational_theories/Generated/All4x4Tables/Refutation644.lean)
- [equational_theories/Generated/All4x4Tables/Refutation645.lean](../../equational_theories/Generated/All4x4Tables/Refutation645.lean)
- [equational_theories/Generated/All4x4Tables/Refutation646.lean](../../equational_theories/Generated/All4x4Tables/Refutation646.lean)
- [equational_theories/Generated/All4x4Tables/Refutation647.lean](../../equational_theories/Generated/All4x4Tables/Refutation647.lean)
- [equational_theories/Generated/All4x4Tables/Refutation648.lean](../../equational_theories/Generated/All4x4Tables/Refutation648.lean)
- [equational_theories/Generated/All4x4Tables/Refutation649.lean](../../equational_theories/Generated/All4x4Tables/Refutation649.lean)
- [equational_theories/Generated/All4x4Tables/Refutation65.lean](../../equational_theories/Generated/All4x4Tables/Refutation65.lean)
- [equational_theories/Generated/All4x4Tables/Refutation650.lean](../../equational_theories/Generated/All4x4Tables/Refutation650.lean)
- [equational_theories/Generated/All4x4Tables/Refutation651.lean](../../equational_theories/Generated/All4x4Tables/Refutation651.lean)
- [equational_theories/Generated/All4x4Tables/Refutation652.lean](../../equational_theories/Generated/All4x4Tables/Refutation652.lean)
- [equational_theories/Generated/All4x4Tables/Refutation653.lean](../../equational_theories/Generated/All4x4Tables/Refutation653.lean)
- [equational_theories/Generated/All4x4Tables/Refutation654.lean](../../equational_theories/Generated/All4x4Tables/Refutation654.lean)
- [equational_theories/Generated/All4x4Tables/Refutation655.lean](../../equational_theories/Generated/All4x4Tables/Refutation655.lean)
- [equational_theories/Generated/All4x4Tables/Refutation656.lean](../../equational_theories/Generated/All4x4Tables/Refutation656.lean)
- [equational_theories/Generated/All4x4Tables/Refutation657.lean](../../equational_theories/Generated/All4x4Tables/Refutation657.lean)
- [equational_theories/Generated/All4x4Tables/Refutation658.lean](../../equational_theories/Generated/All4x4Tables/Refutation658.lean)
- [equational_theories/Generated/All4x4Tables/Refutation659.lean](../../equational_theories/Generated/All4x4Tables/Refutation659.lean)
- [equational_theories/Generated/All4x4Tables/Refutation66.lean](../../equational_theories/Generated/All4x4Tables/Refutation66.lean)
- [equational_theories/Generated/All4x4Tables/Refutation660.lean](../../equational_theories/Generated/All4x4Tables/Refutation660.lean)
- [equational_theories/Generated/All4x4Tables/Refutation661.lean](../../equational_theories/Generated/All4x4Tables/Refutation661.lean)
- [equational_theories/Generated/All4x4Tables/Refutation662.lean](../../equational_theories/Generated/All4x4Tables/Refutation662.lean)
- [equational_theories/Generated/All4x4Tables/Refutation663.lean](../../equational_theories/Generated/All4x4Tables/Refutation663.lean)
- [equational_theories/Generated/All4x4Tables/Refutation664.lean](../../equational_theories/Generated/All4x4Tables/Refutation664.lean)
- [equational_theories/Generated/All4x4Tables/Refutation665.lean](../../equational_theories/Generated/All4x4Tables/Refutation665.lean)
- [equational_theories/Generated/All4x4Tables/Refutation666.lean](../../equational_theories/Generated/All4x4Tables/Refutation666.lean)
- [equational_theories/Generated/All4x4Tables/Refutation667.lean](../../equational_theories/Generated/All4x4Tables/Refutation667.lean)
- [equational_theories/Generated/All4x4Tables/Refutation668.lean](../../equational_theories/Generated/All4x4Tables/Refutation668.lean)
- [equational_theories/Generated/All4x4Tables/Refutation669.lean](../../equational_theories/Generated/All4x4Tables/Refutation669.lean)
- [equational_theories/Generated/All4x4Tables/Refutation67.lean](../../equational_theories/Generated/All4x4Tables/Refutation67.lean)
- [equational_theories/Generated/All4x4Tables/Refutation670.lean](../../equational_theories/Generated/All4x4Tables/Refutation670.lean)
- [equational_theories/Generated/All4x4Tables/Refutation671.lean](../../equational_theories/Generated/All4x4Tables/Refutation671.lean)
- [equational_theories/Generated/All4x4Tables/Refutation672.lean](../../equational_theories/Generated/All4x4Tables/Refutation672.lean)
- [equational_theories/Generated/All4x4Tables/Refutation673.lean](../../equational_theories/Generated/All4x4Tables/Refutation673.lean)
- [equational_theories/Generated/All4x4Tables/Refutation674.lean](../../equational_theories/Generated/All4x4Tables/Refutation674.lean)
- [equational_theories/Generated/All4x4Tables/Refutation675.lean](../../equational_theories/Generated/All4x4Tables/Refutation675.lean)
- [equational_theories/Generated/All4x4Tables/Refutation676.lean](../../equational_theories/Generated/All4x4Tables/Refutation676.lean)
- [equational_theories/Generated/All4x4Tables/Refutation677.lean](../../equational_theories/Generated/All4x4Tables/Refutation677.lean)
- [equational_theories/Generated/All4x4Tables/Refutation678.lean](../../equational_theories/Generated/All4x4Tables/Refutation678.lean)
- [equational_theories/Generated/All4x4Tables/Refutation679.lean](../../equational_theories/Generated/All4x4Tables/Refutation679.lean)
- [equational_theories/Generated/All4x4Tables/Refutation68.lean](../../equational_theories/Generated/All4x4Tables/Refutation68.lean)
- [equational_theories/Generated/All4x4Tables/Refutation680.lean](../../equational_theories/Generated/All4x4Tables/Refutation680.lean)
- [equational_theories/Generated/All4x4Tables/Refutation681.lean](../../equational_theories/Generated/All4x4Tables/Refutation681.lean)
- [equational_theories/Generated/All4x4Tables/Refutation682.lean](../../equational_theories/Generated/All4x4Tables/Refutation682.lean)
- [equational_theories/Generated/All4x4Tables/Refutation683.lean](../../equational_theories/Generated/All4x4Tables/Refutation683.lean)
- [equational_theories/Generated/All4x4Tables/Refutation684.lean](../../equational_theories/Generated/All4x4Tables/Refutation684.lean)
- [equational_theories/Generated/All4x4Tables/Refutation685.lean](../../equational_theories/Generated/All4x4Tables/Refutation685.lean)
- [equational_theories/Generated/All4x4Tables/Refutation686.lean](../../equational_theories/Generated/All4x4Tables/Refutation686.lean)
- [equational_theories/Generated/All4x4Tables/Refutation687.lean](../../equational_theories/Generated/All4x4Tables/Refutation687.lean)
- [equational_theories/Generated/All4x4Tables/Refutation688.lean](../../equational_theories/Generated/All4x4Tables/Refutation688.lean)
- [equational_theories/Generated/All4x4Tables/Refutation689.lean](../../equational_theories/Generated/All4x4Tables/Refutation689.lean)
- [equational_theories/Generated/All4x4Tables/Refutation69.lean](../../equational_theories/Generated/All4x4Tables/Refutation69.lean)
- [equational_theories/Generated/All4x4Tables/Refutation690.lean](../../equational_theories/Generated/All4x4Tables/Refutation690.lean)
- [equational_theories/Generated/All4x4Tables/Refutation691.lean](../../equational_theories/Generated/All4x4Tables/Refutation691.lean)
- [equational_theories/Generated/All4x4Tables/Refutation692.lean](../../equational_theories/Generated/All4x4Tables/Refutation692.lean)
- [equational_theories/Generated/All4x4Tables/Refutation693.lean](../../equational_theories/Generated/All4x4Tables/Refutation693.lean)
- [equational_theories/Generated/All4x4Tables/Refutation694.lean](../../equational_theories/Generated/All4x4Tables/Refutation694.lean)
- [equational_theories/Generated/All4x4Tables/Refutation695.lean](../../equational_theories/Generated/All4x4Tables/Refutation695.lean)
- [equational_theories/Generated/All4x4Tables/Refutation696.lean](../../equational_theories/Generated/All4x4Tables/Refutation696.lean)
- [equational_theories/Generated/All4x4Tables/Refutation697.lean](../../equational_theories/Generated/All4x4Tables/Refutation697.lean)
- [equational_theories/Generated/All4x4Tables/Refutation698.lean](../../equational_theories/Generated/All4x4Tables/Refutation698.lean)
- [equational_theories/Generated/All4x4Tables/Refutation699.lean](../../equational_theories/Generated/All4x4Tables/Refutation699.lean)
- [equational_theories/Generated/All4x4Tables/Refutation7.lean](../../equational_theories/Generated/All4x4Tables/Refutation7.lean)
- [equational_theories/Generated/All4x4Tables/Refutation70.lean](../../equational_theories/Generated/All4x4Tables/Refutation70.lean)
- [equational_theories/Generated/All4x4Tables/Refutation700.lean](../../equational_theories/Generated/All4x4Tables/Refutation700.lean)
- [equational_theories/Generated/All4x4Tables/Refutation701.lean](../../equational_theories/Generated/All4x4Tables/Refutation701.lean)
- [equational_theories/Generated/All4x4Tables/Refutation702.lean](../../equational_theories/Generated/All4x4Tables/Refutation702.lean)
- [equational_theories/Generated/All4x4Tables/Refutation703.lean](../../equational_theories/Generated/All4x4Tables/Refutation703.lean)
- [equational_theories/Generated/All4x4Tables/Refutation704.lean](../../equational_theories/Generated/All4x4Tables/Refutation704.lean)
- [equational_theories/Generated/All4x4Tables/Refutation705.lean](../../equational_theories/Generated/All4x4Tables/Refutation705.lean)
- [equational_theories/Generated/All4x4Tables/Refutation706.lean](../../equational_theories/Generated/All4x4Tables/Refutation706.lean)
- [equational_theories/Generated/All4x4Tables/Refutation707.lean](../../equational_theories/Generated/All4x4Tables/Refutation707.lean)
- [equational_theories/Generated/All4x4Tables/Refutation708.lean](../../equational_theories/Generated/All4x4Tables/Refutation708.lean)
- [equational_theories/Generated/All4x4Tables/Refutation709.lean](../../equational_theories/Generated/All4x4Tables/Refutation709.lean)
- [equational_theories/Generated/All4x4Tables/Refutation71.lean](../../equational_theories/Generated/All4x4Tables/Refutation71.lean)
- [equational_theories/Generated/All4x4Tables/Refutation710.lean](../../equational_theories/Generated/All4x4Tables/Refutation710.lean)
- [equational_theories/Generated/All4x4Tables/Refutation711.lean](../../equational_theories/Generated/All4x4Tables/Refutation711.lean)
- [equational_theories/Generated/All4x4Tables/Refutation712.lean](../../equational_theories/Generated/All4x4Tables/Refutation712.lean)
- [equational_theories/Generated/All4x4Tables/Refutation713.lean](../../equational_theories/Generated/All4x4Tables/Refutation713.lean)
- [equational_theories/Generated/All4x4Tables/Refutation714.lean](../../equational_theories/Generated/All4x4Tables/Refutation714.lean)
- [equational_theories/Generated/All4x4Tables/Refutation715.lean](../../equational_theories/Generated/All4x4Tables/Refutation715.lean)
- [equational_theories/Generated/All4x4Tables/Refutation716.lean](../../equational_theories/Generated/All4x4Tables/Refutation716.lean)
- [equational_theories/Generated/All4x4Tables/Refutation717.lean](../../equational_theories/Generated/All4x4Tables/Refutation717.lean)
- [equational_theories/Generated/All4x4Tables/Refutation718.lean](../../equational_theories/Generated/All4x4Tables/Refutation718.lean)
- [equational_theories/Generated/All4x4Tables/Refutation719.lean](../../equational_theories/Generated/All4x4Tables/Refutation719.lean)
- [equational_theories/Generated/All4x4Tables/Refutation72.lean](../../equational_theories/Generated/All4x4Tables/Refutation72.lean)
- [equational_theories/Generated/All4x4Tables/Refutation720.lean](../../equational_theories/Generated/All4x4Tables/Refutation720.lean)
- [equational_theories/Generated/All4x4Tables/Refutation721.lean](../../equational_theories/Generated/All4x4Tables/Refutation721.lean)
- [equational_theories/Generated/All4x4Tables/Refutation722.lean](../../equational_theories/Generated/All4x4Tables/Refutation722.lean)
- [equational_theories/Generated/All4x4Tables/Refutation723.lean](../../equational_theories/Generated/All4x4Tables/Refutation723.lean)
- [equational_theories/Generated/All4x4Tables/Refutation724.lean](../../equational_theories/Generated/All4x4Tables/Refutation724.lean)
- [equational_theories/Generated/All4x4Tables/Refutation725.lean](../../equational_theories/Generated/All4x4Tables/Refutation725.lean)
- [equational_theories/Generated/All4x4Tables/Refutation726.lean](../../equational_theories/Generated/All4x4Tables/Refutation726.lean)
- [equational_theories/Generated/All4x4Tables/Refutation727.lean](../../equational_theories/Generated/All4x4Tables/Refutation727.lean)
- [equational_theories/Generated/All4x4Tables/Refutation728.lean](../../equational_theories/Generated/All4x4Tables/Refutation728.lean)
- [equational_theories/Generated/All4x4Tables/Refutation729.lean](../../equational_theories/Generated/All4x4Tables/Refutation729.lean)
- [equational_theories/Generated/All4x4Tables/Refutation73.lean](../../equational_theories/Generated/All4x4Tables/Refutation73.lean)
- [equational_theories/Generated/All4x4Tables/Refutation730.lean](../../equational_theories/Generated/All4x4Tables/Refutation730.lean)
- [equational_theories/Generated/All4x4Tables/Refutation731.lean](../../equational_theories/Generated/All4x4Tables/Refutation731.lean)
- [equational_theories/Generated/All4x4Tables/Refutation732.lean](../../equational_theories/Generated/All4x4Tables/Refutation732.lean)
- [equational_theories/Generated/All4x4Tables/Refutation733.lean](../../equational_theories/Generated/All4x4Tables/Refutation733.lean)
- [equational_theories/Generated/All4x4Tables/Refutation734.lean](../../equational_theories/Generated/All4x4Tables/Refutation734.lean)
- [equational_theories/Generated/All4x4Tables/Refutation735.lean](../../equational_theories/Generated/All4x4Tables/Refutation735.lean)
- [equational_theories/Generated/All4x4Tables/Refutation736.lean](../../equational_theories/Generated/All4x4Tables/Refutation736.lean)
- [equational_theories/Generated/All4x4Tables/Refutation737.lean](../../equational_theories/Generated/All4x4Tables/Refutation737.lean)
- [equational_theories/Generated/All4x4Tables/Refutation738.lean](../../equational_theories/Generated/All4x4Tables/Refutation738.lean)
- [equational_theories/Generated/All4x4Tables/Refutation739.lean](../../equational_theories/Generated/All4x4Tables/Refutation739.lean)
- [equational_theories/Generated/All4x4Tables/Refutation74.lean](../../equational_theories/Generated/All4x4Tables/Refutation74.lean)
- [equational_theories/Generated/All4x4Tables/Refutation740.lean](../../equational_theories/Generated/All4x4Tables/Refutation740.lean)
- [equational_theories/Generated/All4x4Tables/Refutation741.lean](../../equational_theories/Generated/All4x4Tables/Refutation741.lean)
- [equational_theories/Generated/All4x4Tables/Refutation742.lean](../../equational_theories/Generated/All4x4Tables/Refutation742.lean)
- [equational_theories/Generated/All4x4Tables/Refutation743.lean](../../equational_theories/Generated/All4x4Tables/Refutation743.lean)
- [equational_theories/Generated/All4x4Tables/Refutation744.lean](../../equational_theories/Generated/All4x4Tables/Refutation744.lean)
- [equational_theories/Generated/All4x4Tables/Refutation745.lean](../../equational_theories/Generated/All4x4Tables/Refutation745.lean)
- [equational_theories/Generated/All4x4Tables/Refutation746.lean](../../equational_theories/Generated/All4x4Tables/Refutation746.lean)
- [equational_theories/Generated/All4x4Tables/Refutation747.lean](../../equational_theories/Generated/All4x4Tables/Refutation747.lean)
- [equational_theories/Generated/All4x4Tables/Refutation748.lean](../../equational_theories/Generated/All4x4Tables/Refutation748.lean)
- [equational_theories/Generated/All4x4Tables/Refutation749.lean](../../equational_theories/Generated/All4x4Tables/Refutation749.lean)
- [equational_theories/Generated/All4x4Tables/Refutation75.lean](../../equational_theories/Generated/All4x4Tables/Refutation75.lean)
- [equational_theories/Generated/All4x4Tables/Refutation750.lean](../../equational_theories/Generated/All4x4Tables/Refutation750.lean)
- [equational_theories/Generated/All4x4Tables/Refutation751.lean](../../equational_theories/Generated/All4x4Tables/Refutation751.lean)
- [equational_theories/Generated/All4x4Tables/Refutation752.lean](../../equational_theories/Generated/All4x4Tables/Refutation752.lean)
- [equational_theories/Generated/All4x4Tables/Refutation753.lean](../../equational_theories/Generated/All4x4Tables/Refutation753.lean)
- [equational_theories/Generated/All4x4Tables/Refutation754.lean](../../equational_theories/Generated/All4x4Tables/Refutation754.lean)
- [equational_theories/Generated/All4x4Tables/Refutation755.lean](../../equational_theories/Generated/All4x4Tables/Refutation755.lean)
- [equational_theories/Generated/All4x4Tables/Refutation756.lean](../../equational_theories/Generated/All4x4Tables/Refutation756.lean)
- [equational_theories/Generated/All4x4Tables/Refutation757.lean](../../equational_theories/Generated/All4x4Tables/Refutation757.lean)
- [equational_theories/Generated/All4x4Tables/Refutation758.lean](../../equational_theories/Generated/All4x4Tables/Refutation758.lean)
- [equational_theories/Generated/All4x4Tables/Refutation759.lean](../../equational_theories/Generated/All4x4Tables/Refutation759.lean)
- [equational_theories/Generated/All4x4Tables/Refutation76.lean](../../equational_theories/Generated/All4x4Tables/Refutation76.lean)
- [equational_theories/Generated/All4x4Tables/Refutation760.lean](../../equational_theories/Generated/All4x4Tables/Refutation760.lean)
- [equational_theories/Generated/All4x4Tables/Refutation761.lean](../../equational_theories/Generated/All4x4Tables/Refutation761.lean)
- [equational_theories/Generated/All4x4Tables/Refutation762.lean](../../equational_theories/Generated/All4x4Tables/Refutation762.lean)
- [equational_theories/Generated/All4x4Tables/Refutation763.lean](../../equational_theories/Generated/All4x4Tables/Refutation763.lean)
- [equational_theories/Generated/All4x4Tables/Refutation764.lean](../../equational_theories/Generated/All4x4Tables/Refutation764.lean)
- [equational_theories/Generated/All4x4Tables/Refutation765.lean](../../equational_theories/Generated/All4x4Tables/Refutation765.lean)
- [equational_theories/Generated/All4x4Tables/Refutation766.lean](../../equational_theories/Generated/All4x4Tables/Refutation766.lean)
- [equational_theories/Generated/All4x4Tables/Refutation767.lean](../../equational_theories/Generated/All4x4Tables/Refutation767.lean)
- [equational_theories/Generated/All4x4Tables/Refutation768.lean](../../equational_theories/Generated/All4x4Tables/Refutation768.lean)
- [equational_theories/Generated/All4x4Tables/Refutation769.lean](../../equational_theories/Generated/All4x4Tables/Refutation769.lean)
- [equational_theories/Generated/All4x4Tables/Refutation77.lean](../../equational_theories/Generated/All4x4Tables/Refutation77.lean)
- [equational_theories/Generated/All4x4Tables/Refutation770.lean](../../equational_theories/Generated/All4x4Tables/Refutation770.lean)
- [equational_theories/Generated/All4x4Tables/Refutation771.lean](../../equational_theories/Generated/All4x4Tables/Refutation771.lean)
- [equational_theories/Generated/All4x4Tables/Refutation772.lean](../../equational_theories/Generated/All4x4Tables/Refutation772.lean)
- [equational_theories/Generated/All4x4Tables/Refutation773.lean](../../equational_theories/Generated/All4x4Tables/Refutation773.lean)
- [equational_theories/Generated/All4x4Tables/Refutation774.lean](../../equational_theories/Generated/All4x4Tables/Refutation774.lean)
- [equational_theories/Generated/All4x4Tables/Refutation775.lean](../../equational_theories/Generated/All4x4Tables/Refutation775.lean)
- [equational_theories/Generated/All4x4Tables/Refutation776.lean](../../equational_theories/Generated/All4x4Tables/Refutation776.lean)
- [equational_theories/Generated/All4x4Tables/Refutation777.lean](../../equational_theories/Generated/All4x4Tables/Refutation777.lean)
- [equational_theories/Generated/All4x4Tables/Refutation778.lean](../../equational_theories/Generated/All4x4Tables/Refutation778.lean)
- [equational_theories/Generated/All4x4Tables/Refutation779.lean](../../equational_theories/Generated/All4x4Tables/Refutation779.lean)
- [equational_theories/Generated/All4x4Tables/Refutation78.lean](../../equational_theories/Generated/All4x4Tables/Refutation78.lean)
- [equational_theories/Generated/All4x4Tables/Refutation780.lean](../../equational_theories/Generated/All4x4Tables/Refutation780.lean)
- [equational_theories/Generated/All4x4Tables/Refutation781.lean](../../equational_theories/Generated/All4x4Tables/Refutation781.lean)
- [equational_theories/Generated/All4x4Tables/Refutation782.lean](../../equational_theories/Generated/All4x4Tables/Refutation782.lean)
- [equational_theories/Generated/All4x4Tables/Refutation783.lean](../../equational_theories/Generated/All4x4Tables/Refutation783.lean)
- [equational_theories/Generated/All4x4Tables/Refutation784.lean](../../equational_theories/Generated/All4x4Tables/Refutation784.lean)
- [equational_theories/Generated/All4x4Tables/Refutation785.lean](../../equational_theories/Generated/All4x4Tables/Refutation785.lean)
- [equational_theories/Generated/All4x4Tables/Refutation786.lean](../../equational_theories/Generated/All4x4Tables/Refutation786.lean)
- [equational_theories/Generated/All4x4Tables/Refutation787.lean](../../equational_theories/Generated/All4x4Tables/Refutation787.lean)
- [equational_theories/Generated/All4x4Tables/Refutation788.lean](../../equational_theories/Generated/All4x4Tables/Refutation788.lean)
- [equational_theories/Generated/All4x4Tables/Refutation789.lean](../../equational_theories/Generated/All4x4Tables/Refutation789.lean)
- [equational_theories/Generated/All4x4Tables/Refutation79.lean](../../equational_theories/Generated/All4x4Tables/Refutation79.lean)
- [equational_theories/Generated/All4x4Tables/Refutation790.lean](../../equational_theories/Generated/All4x4Tables/Refutation790.lean)
- [equational_theories/Generated/All4x4Tables/Refutation791.lean](../../equational_theories/Generated/All4x4Tables/Refutation791.lean)
- [equational_theories/Generated/All4x4Tables/Refutation792.lean](../../equational_theories/Generated/All4x4Tables/Refutation792.lean)
- [equational_theories/Generated/All4x4Tables/Refutation793.lean](../../equational_theories/Generated/All4x4Tables/Refutation793.lean)
- [equational_theories/Generated/All4x4Tables/Refutation794.lean](../../equational_theories/Generated/All4x4Tables/Refutation794.lean)
- [equational_theories/Generated/All4x4Tables/Refutation795.lean](../../equational_theories/Generated/All4x4Tables/Refutation795.lean)
- [equational_theories/Generated/All4x4Tables/Refutation796.lean](../../equational_theories/Generated/All4x4Tables/Refutation796.lean)
- [equational_theories/Generated/All4x4Tables/Refutation797.lean](../../equational_theories/Generated/All4x4Tables/Refutation797.lean)
- [equational_theories/Generated/All4x4Tables/Refutation798.lean](../../equational_theories/Generated/All4x4Tables/Refutation798.lean)
- [equational_theories/Generated/All4x4Tables/Refutation799.lean](../../equational_theories/Generated/All4x4Tables/Refutation799.lean)
- [equational_theories/Generated/All4x4Tables/Refutation8.lean](../../equational_theories/Generated/All4x4Tables/Refutation8.lean)
- [equational_theories/Generated/All4x4Tables/Refutation80.lean](../../equational_theories/Generated/All4x4Tables/Refutation80.lean)
- [equational_theories/Generated/All4x4Tables/Refutation800.lean](../../equational_theories/Generated/All4x4Tables/Refutation800.lean)
- [equational_theories/Generated/All4x4Tables/Refutation801.lean](../../equational_theories/Generated/All4x4Tables/Refutation801.lean)
- [equational_theories/Generated/All4x4Tables/Refutation802.lean](../../equational_theories/Generated/All4x4Tables/Refutation802.lean)
- [equational_theories/Generated/All4x4Tables/Refutation803.lean](../../equational_theories/Generated/All4x4Tables/Refutation803.lean)
- [equational_theories/Generated/All4x4Tables/Refutation804.lean](../../equational_theories/Generated/All4x4Tables/Refutation804.lean)
- [equational_theories/Generated/All4x4Tables/Refutation805.lean](../../equational_theories/Generated/All4x4Tables/Refutation805.lean)
- [equational_theories/Generated/All4x4Tables/Refutation806.lean](../../equational_theories/Generated/All4x4Tables/Refutation806.lean)
- [equational_theories/Generated/All4x4Tables/Refutation807.lean](../../equational_theories/Generated/All4x4Tables/Refutation807.lean)
- [equational_theories/Generated/All4x4Tables/Refutation808.lean](../../equational_theories/Generated/All4x4Tables/Refutation808.lean)
- [equational_theories/Generated/All4x4Tables/Refutation809.lean](../../equational_theories/Generated/All4x4Tables/Refutation809.lean)
- [equational_theories/Generated/All4x4Tables/Refutation81.lean](../../equational_theories/Generated/All4x4Tables/Refutation81.lean)
- [equational_theories/Generated/All4x4Tables/Refutation810.lean](../../equational_theories/Generated/All4x4Tables/Refutation810.lean)
- [equational_theories/Generated/All4x4Tables/Refutation811.lean](../../equational_theories/Generated/All4x4Tables/Refutation811.lean)
- [equational_theories/Generated/All4x4Tables/Refutation812.lean](../../equational_theories/Generated/All4x4Tables/Refutation812.lean)
- [equational_theories/Generated/All4x4Tables/Refutation813.lean](../../equational_theories/Generated/All4x4Tables/Refutation813.lean)
- [equational_theories/Generated/All4x4Tables/Refutation814.lean](../../equational_theories/Generated/All4x4Tables/Refutation814.lean)
- [equational_theories/Generated/All4x4Tables/Refutation815.lean](../../equational_theories/Generated/All4x4Tables/Refutation815.lean)
- [equational_theories/Generated/All4x4Tables/Refutation816.lean](../../equational_theories/Generated/All4x4Tables/Refutation816.lean)
- [equational_theories/Generated/All4x4Tables/Refutation817.lean](../../equational_theories/Generated/All4x4Tables/Refutation817.lean)
- [equational_theories/Generated/All4x4Tables/Refutation818.lean](../../equational_theories/Generated/All4x4Tables/Refutation818.lean)
- [equational_theories/Generated/All4x4Tables/Refutation819.lean](../../equational_theories/Generated/All4x4Tables/Refutation819.lean)
- [equational_theories/Generated/All4x4Tables/Refutation82.lean](../../equational_theories/Generated/All4x4Tables/Refutation82.lean)
- [equational_theories/Generated/All4x4Tables/Refutation820.lean](../../equational_theories/Generated/All4x4Tables/Refutation820.lean)
- [equational_theories/Generated/All4x4Tables/Refutation821.lean](../../equational_theories/Generated/All4x4Tables/Refutation821.lean)
- [equational_theories/Generated/All4x4Tables/Refutation822.lean](../../equational_theories/Generated/All4x4Tables/Refutation822.lean)
- [equational_theories/Generated/All4x4Tables/Refutation823.lean](../../equational_theories/Generated/All4x4Tables/Refutation823.lean)
- [equational_theories/Generated/All4x4Tables/Refutation824.lean](../../equational_theories/Generated/All4x4Tables/Refutation824.lean)
- [equational_theories/Generated/All4x4Tables/Refutation825.lean](../../equational_theories/Generated/All4x4Tables/Refutation825.lean)
- [equational_theories/Generated/All4x4Tables/Refutation826.lean](../../equational_theories/Generated/All4x4Tables/Refutation826.lean)
- [equational_theories/Generated/All4x4Tables/Refutation827.lean](../../equational_theories/Generated/All4x4Tables/Refutation827.lean)
- [equational_theories/Generated/All4x4Tables/Refutation828.lean](../../equational_theories/Generated/All4x4Tables/Refutation828.lean)
- [equational_theories/Generated/All4x4Tables/Refutation829.lean](../../equational_theories/Generated/All4x4Tables/Refutation829.lean)
- [equational_theories/Generated/All4x4Tables/Refutation83.lean](../../equational_theories/Generated/All4x4Tables/Refutation83.lean)
- [equational_theories/Generated/All4x4Tables/Refutation830.lean](../../equational_theories/Generated/All4x4Tables/Refutation830.lean)
- [equational_theories/Generated/All4x4Tables/Refutation831.lean](../../equational_theories/Generated/All4x4Tables/Refutation831.lean)
- [equational_theories/Generated/All4x4Tables/Refutation832.lean](../../equational_theories/Generated/All4x4Tables/Refutation832.lean)
- [equational_theories/Generated/All4x4Tables/Refutation833.lean](../../equational_theories/Generated/All4x4Tables/Refutation833.lean)
- [equational_theories/Generated/All4x4Tables/Refutation834.lean](../../equational_theories/Generated/All4x4Tables/Refutation834.lean)
- [equational_theories/Generated/All4x4Tables/Refutation835.lean](../../equational_theories/Generated/All4x4Tables/Refutation835.lean)
- [equational_theories/Generated/All4x4Tables/Refutation836.lean](../../equational_theories/Generated/All4x4Tables/Refutation836.lean)
- [equational_theories/Generated/All4x4Tables/Refutation837.lean](../../equational_theories/Generated/All4x4Tables/Refutation837.lean)
- [equational_theories/Generated/All4x4Tables/Refutation838.lean](../../equational_theories/Generated/All4x4Tables/Refutation838.lean)
- [equational_theories/Generated/All4x4Tables/Refutation839.lean](../../equational_theories/Generated/All4x4Tables/Refutation839.lean)
- [equational_theories/Generated/All4x4Tables/Refutation84.lean](../../equational_theories/Generated/All4x4Tables/Refutation84.lean)
- [equational_theories/Generated/All4x4Tables/Refutation840.lean](../../equational_theories/Generated/All4x4Tables/Refutation840.lean)
- [equational_theories/Generated/All4x4Tables/Refutation841.lean](../../equational_theories/Generated/All4x4Tables/Refutation841.lean)
- [equational_theories/Generated/All4x4Tables/Refutation842.lean](../../equational_theories/Generated/All4x4Tables/Refutation842.lean)
- [equational_theories/Generated/All4x4Tables/Refutation843.lean](../../equational_theories/Generated/All4x4Tables/Refutation843.lean)
- [equational_theories/Generated/All4x4Tables/Refutation844.lean](../../equational_theories/Generated/All4x4Tables/Refutation844.lean)
- [equational_theories/Generated/All4x4Tables/Refutation845.lean](../../equational_theories/Generated/All4x4Tables/Refutation845.lean)
- [equational_theories/Generated/All4x4Tables/Refutation846.lean](../../equational_theories/Generated/All4x4Tables/Refutation846.lean)
- [equational_theories/Generated/All4x4Tables/Refutation847.lean](../../equational_theories/Generated/All4x4Tables/Refutation847.lean)
- [equational_theories/Generated/All4x4Tables/Refutation848.lean](../../equational_theories/Generated/All4x4Tables/Refutation848.lean)
- [equational_theories/Generated/All4x4Tables/Refutation849.lean](../../equational_theories/Generated/All4x4Tables/Refutation849.lean)
- [equational_theories/Generated/All4x4Tables/Refutation85.lean](../../equational_theories/Generated/All4x4Tables/Refutation85.lean)
- [equational_theories/Generated/All4x4Tables/Refutation850.lean](../../equational_theories/Generated/All4x4Tables/Refutation850.lean)
- [equational_theories/Generated/All4x4Tables/Refutation851.lean](../../equational_theories/Generated/All4x4Tables/Refutation851.lean)
- [equational_theories/Generated/All4x4Tables/Refutation852.lean](../../equational_theories/Generated/All4x4Tables/Refutation852.lean)
- [equational_theories/Generated/All4x4Tables/Refutation853.lean](../../equational_theories/Generated/All4x4Tables/Refutation853.lean)
- [equational_theories/Generated/All4x4Tables/Refutation854.lean](../../equational_theories/Generated/All4x4Tables/Refutation854.lean)
- [equational_theories/Generated/All4x4Tables/Refutation855.lean](../../equational_theories/Generated/All4x4Tables/Refutation855.lean)
- [equational_theories/Generated/All4x4Tables/Refutation856.lean](../../equational_theories/Generated/All4x4Tables/Refutation856.lean)
- [equational_theories/Generated/All4x4Tables/Refutation857.lean](../../equational_theories/Generated/All4x4Tables/Refutation857.lean)
- [equational_theories/Generated/All4x4Tables/Refutation858.lean](../../equational_theories/Generated/All4x4Tables/Refutation858.lean)
- [equational_theories/Generated/All4x4Tables/Refutation859.lean](../../equational_theories/Generated/All4x4Tables/Refutation859.lean)
- [equational_theories/Generated/All4x4Tables/Refutation86.lean](../../equational_theories/Generated/All4x4Tables/Refutation86.lean)
- [equational_theories/Generated/All4x4Tables/Refutation860.lean](../../equational_theories/Generated/All4x4Tables/Refutation860.lean)
- [equational_theories/Generated/All4x4Tables/Refutation861.lean](../../equational_theories/Generated/All4x4Tables/Refutation861.lean)
- [equational_theories/Generated/All4x4Tables/Refutation862.lean](../../equational_theories/Generated/All4x4Tables/Refutation862.lean)
- [equational_theories/Generated/All4x4Tables/Refutation863.lean](../../equational_theories/Generated/All4x4Tables/Refutation863.lean)
- [equational_theories/Generated/All4x4Tables/Refutation864.lean](../../equational_theories/Generated/All4x4Tables/Refutation864.lean)
- [equational_theories/Generated/All4x4Tables/Refutation865.lean](../../equational_theories/Generated/All4x4Tables/Refutation865.lean)
- [equational_theories/Generated/All4x4Tables/Refutation866.lean](../../equational_theories/Generated/All4x4Tables/Refutation866.lean)
- [equational_theories/Generated/All4x4Tables/Refutation867.lean](../../equational_theories/Generated/All4x4Tables/Refutation867.lean)
- [equational_theories/Generated/All4x4Tables/Refutation868.lean](../../equational_theories/Generated/All4x4Tables/Refutation868.lean)
- [equational_theories/Generated/All4x4Tables/Refutation869.lean](../../equational_theories/Generated/All4x4Tables/Refutation869.lean)
- [equational_theories/Generated/All4x4Tables/Refutation87.lean](../../equational_theories/Generated/All4x4Tables/Refutation87.lean)
- [equational_theories/Generated/All4x4Tables/Refutation870.lean](../../equational_theories/Generated/All4x4Tables/Refutation870.lean)
- [equational_theories/Generated/All4x4Tables/Refutation871.lean](../../equational_theories/Generated/All4x4Tables/Refutation871.lean)
- [equational_theories/Generated/All4x4Tables/Refutation872.lean](../../equational_theories/Generated/All4x4Tables/Refutation872.lean)
- [equational_theories/Generated/All4x4Tables/Refutation873.lean](../../equational_theories/Generated/All4x4Tables/Refutation873.lean)
- [equational_theories/Generated/All4x4Tables/Refutation874.lean](../../equational_theories/Generated/All4x4Tables/Refutation874.lean)
- [equational_theories/Generated/All4x4Tables/Refutation875.lean](../../equational_theories/Generated/All4x4Tables/Refutation875.lean)
- [equational_theories/Generated/All4x4Tables/Refutation876.lean](../../equational_theories/Generated/All4x4Tables/Refutation876.lean)
- [equational_theories/Generated/All4x4Tables/Refutation877.lean](../../equational_theories/Generated/All4x4Tables/Refutation877.lean)
- [equational_theories/Generated/All4x4Tables/Refutation878.lean](../../equational_theories/Generated/All4x4Tables/Refutation878.lean)
- [equational_theories/Generated/All4x4Tables/Refutation879.lean](../../equational_theories/Generated/All4x4Tables/Refutation879.lean)
- [equational_theories/Generated/All4x4Tables/Refutation88.lean](../../equational_theories/Generated/All4x4Tables/Refutation88.lean)
- [equational_theories/Generated/All4x4Tables/Refutation880.lean](../../equational_theories/Generated/All4x4Tables/Refutation880.lean)
- [equational_theories/Generated/All4x4Tables/Refutation881.lean](../../equational_theories/Generated/All4x4Tables/Refutation881.lean)
- [equational_theories/Generated/All4x4Tables/Refutation882.lean](../../equational_theories/Generated/All4x4Tables/Refutation882.lean)
- [equational_theories/Generated/All4x4Tables/Refutation883.lean](../../equational_theories/Generated/All4x4Tables/Refutation883.lean)
- [equational_theories/Generated/All4x4Tables/Refutation884.lean](../../equational_theories/Generated/All4x4Tables/Refutation884.lean)
- [equational_theories/Generated/All4x4Tables/Refutation885.lean](../../equational_theories/Generated/All4x4Tables/Refutation885.lean)
- [equational_theories/Generated/All4x4Tables/Refutation886.lean](../../equational_theories/Generated/All4x4Tables/Refutation886.lean)
- [equational_theories/Generated/All4x4Tables/Refutation887.lean](../../equational_theories/Generated/All4x4Tables/Refutation887.lean)
- [equational_theories/Generated/All4x4Tables/Refutation888.lean](../../equational_theories/Generated/All4x4Tables/Refutation888.lean)
- [equational_theories/Generated/All4x4Tables/Refutation889.lean](../../equational_theories/Generated/All4x4Tables/Refutation889.lean)
- [equational_theories/Generated/All4x4Tables/Refutation89.lean](../../equational_theories/Generated/All4x4Tables/Refutation89.lean)
- [equational_theories/Generated/All4x4Tables/Refutation890.lean](../../equational_theories/Generated/All4x4Tables/Refutation890.lean)
- [equational_theories/Generated/All4x4Tables/Refutation891.lean](../../equational_theories/Generated/All4x4Tables/Refutation891.lean)
- [equational_theories/Generated/All4x4Tables/Refutation892.lean](../../equational_theories/Generated/All4x4Tables/Refutation892.lean)
- [equational_theories/Generated/All4x4Tables/Refutation893.lean](../../equational_theories/Generated/All4x4Tables/Refutation893.lean)
- [equational_theories/Generated/All4x4Tables/Refutation894.lean](../../equational_theories/Generated/All4x4Tables/Refutation894.lean)
- [equational_theories/Generated/All4x4Tables/Refutation895.lean](../../equational_theories/Generated/All4x4Tables/Refutation895.lean)
- [equational_theories/Generated/All4x4Tables/Refutation896.lean](../../equational_theories/Generated/All4x4Tables/Refutation896.lean)
- [equational_theories/Generated/All4x4Tables/Refutation897.lean](../../equational_theories/Generated/All4x4Tables/Refutation897.lean)
- [equational_theories/Generated/All4x4Tables/Refutation898.lean](../../equational_theories/Generated/All4x4Tables/Refutation898.lean)
- [equational_theories/Generated/All4x4Tables/Refutation899.lean](../../equational_theories/Generated/All4x4Tables/Refutation899.lean)
- [equational_theories/Generated/All4x4Tables/Refutation9.lean](../../equational_theories/Generated/All4x4Tables/Refutation9.lean)
- [equational_theories/Generated/All4x4Tables/Refutation90.lean](../../equational_theories/Generated/All4x4Tables/Refutation90.lean)
- [equational_theories/Generated/All4x4Tables/Refutation900.lean](../../equational_theories/Generated/All4x4Tables/Refutation900.lean)
- [equational_theories/Generated/All4x4Tables/Refutation901.lean](../../equational_theories/Generated/All4x4Tables/Refutation901.lean)
- [equational_theories/Generated/All4x4Tables/Refutation902.lean](../../equational_theories/Generated/All4x4Tables/Refutation902.lean)
- [equational_theories/Generated/All4x4Tables/Refutation903.lean](../../equational_theories/Generated/All4x4Tables/Refutation903.lean)
- [equational_theories/Generated/All4x4Tables/Refutation904.lean](../../equational_theories/Generated/All4x4Tables/Refutation904.lean)
- [equational_theories/Generated/All4x4Tables/Refutation905.lean](../../equational_theories/Generated/All4x4Tables/Refutation905.lean)
- [equational_theories/Generated/All4x4Tables/Refutation906.lean](../../equational_theories/Generated/All4x4Tables/Refutation906.lean)
- [equational_theories/Generated/All4x4Tables/Refutation907.lean](../../equational_theories/Generated/All4x4Tables/Refutation907.lean)
- [equational_theories/Generated/All4x4Tables/Refutation908.lean](../../equational_theories/Generated/All4x4Tables/Refutation908.lean)
- [equational_theories/Generated/All4x4Tables/Refutation909.lean](../../equational_theories/Generated/All4x4Tables/Refutation909.lean)
- [equational_theories/Generated/All4x4Tables/Refutation91.lean](../../equational_theories/Generated/All4x4Tables/Refutation91.lean)
- [equational_theories/Generated/All4x4Tables/Refutation910.lean](../../equational_theories/Generated/All4x4Tables/Refutation910.lean)
- [equational_theories/Generated/All4x4Tables/Refutation911.lean](../../equational_theories/Generated/All4x4Tables/Refutation911.lean)
- [equational_theories/Generated/All4x4Tables/Refutation912.lean](../../equational_theories/Generated/All4x4Tables/Refutation912.lean)
- [equational_theories/Generated/All4x4Tables/Refutation913.lean](../../equational_theories/Generated/All4x4Tables/Refutation913.lean)
- [equational_theories/Generated/All4x4Tables/Refutation914.lean](../../equational_theories/Generated/All4x4Tables/Refutation914.lean)
- [equational_theories/Generated/All4x4Tables/Refutation915.lean](../../equational_theories/Generated/All4x4Tables/Refutation915.lean)
- [equational_theories/Generated/All4x4Tables/Refutation916.lean](../../equational_theories/Generated/All4x4Tables/Refutation916.lean)
- [equational_theories/Generated/All4x4Tables/Refutation917.lean](../../equational_theories/Generated/All4x4Tables/Refutation917.lean)
- [equational_theories/Generated/All4x4Tables/Refutation918.lean](../../equational_theories/Generated/All4x4Tables/Refutation918.lean)
- [equational_theories/Generated/All4x4Tables/Refutation919.lean](../../equational_theories/Generated/All4x4Tables/Refutation919.lean)
- [equational_theories/Generated/All4x4Tables/Refutation92.lean](../../equational_theories/Generated/All4x4Tables/Refutation92.lean)
- [equational_theories/Generated/All4x4Tables/Refutation920.lean](../../equational_theories/Generated/All4x4Tables/Refutation920.lean)
- [equational_theories/Generated/All4x4Tables/Refutation921.lean](../../equational_theories/Generated/All4x4Tables/Refutation921.lean)
- [equational_theories/Generated/All4x4Tables/Refutation922.lean](../../equational_theories/Generated/All4x4Tables/Refutation922.lean)
- [equational_theories/Generated/All4x4Tables/Refutation923.lean](../../equational_theories/Generated/All4x4Tables/Refutation923.lean)
- [equational_theories/Generated/All4x4Tables/Refutation924.lean](../../equational_theories/Generated/All4x4Tables/Refutation924.lean)
- [equational_theories/Generated/All4x4Tables/Refutation925.lean](../../equational_theories/Generated/All4x4Tables/Refutation925.lean)
- [equational_theories/Generated/All4x4Tables/Refutation926.lean](../../equational_theories/Generated/All4x4Tables/Refutation926.lean)
- [equational_theories/Generated/All4x4Tables/Refutation927.lean](../../equational_theories/Generated/All4x4Tables/Refutation927.lean)
- [equational_theories/Generated/All4x4Tables/Refutation928.lean](../../equational_theories/Generated/All4x4Tables/Refutation928.lean)
- [equational_theories/Generated/All4x4Tables/Refutation929.lean](../../equational_theories/Generated/All4x4Tables/Refutation929.lean)
- [equational_theories/Generated/All4x4Tables/Refutation93.lean](../../equational_theories/Generated/All4x4Tables/Refutation93.lean)
- [equational_theories/Generated/All4x4Tables/Refutation930.lean](../../equational_theories/Generated/All4x4Tables/Refutation930.lean)
- [equational_theories/Generated/All4x4Tables/Refutation931.lean](../../equational_theories/Generated/All4x4Tables/Refutation931.lean)
- [equational_theories/Generated/All4x4Tables/Refutation932.lean](../../equational_theories/Generated/All4x4Tables/Refutation932.lean)
- [equational_theories/Generated/All4x4Tables/Refutation933.lean](../../equational_theories/Generated/All4x4Tables/Refutation933.lean)
- [equational_theories/Generated/All4x4Tables/Refutation934.lean](../../equational_theories/Generated/All4x4Tables/Refutation934.lean)
- [equational_theories/Generated/All4x4Tables/Refutation935.lean](../../equational_theories/Generated/All4x4Tables/Refutation935.lean)
- [equational_theories/Generated/All4x4Tables/Refutation936.lean](../../equational_theories/Generated/All4x4Tables/Refutation936.lean)
- [equational_theories/Generated/All4x4Tables/Refutation937.lean](../../equational_theories/Generated/All4x4Tables/Refutation937.lean)
- [equational_theories/Generated/All4x4Tables/Refutation938.lean](../../equational_theories/Generated/All4x4Tables/Refutation938.lean)
- [equational_theories/Generated/All4x4Tables/Refutation939.lean](../../equational_theories/Generated/All4x4Tables/Refutation939.lean)
- [equational_theories/Generated/All4x4Tables/Refutation94.lean](../../equational_theories/Generated/All4x4Tables/Refutation94.lean)
- [equational_theories/Generated/All4x4Tables/Refutation95.lean](../../equational_theories/Generated/All4x4Tables/Refutation95.lean)
- [equational_theories/Generated/All4x4Tables/Refutation96.lean](../../equational_theories/Generated/All4x4Tables/Refutation96.lean)
- [equational_theories/Generated/All4x4Tables/Refutation97.lean](../../equational_theories/Generated/All4x4Tables/Refutation97.lean)
- [equational_theories/Generated/All4x4Tables/Refutation98.lean](../../equational_theories/Generated/All4x4Tables/Refutation98.lean)
- [equational_theories/Generated/All4x4Tables/Refutation99.lean](../../equational_theories/Generated/All4x4Tables/Refutation99.lean)
- [equational_theories/Generated/Confluence/ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean)
- [equational_theories/Generated/Constant.lean](../../equational_theories/Generated/Constant.lean)
- [equational_theories/Generated/EquationSearch/theorems/Combined.lean](../../equational_theories/Generated/EquationSearch/theorems/Combined.lean)
- [equational_theories/Generated/FinSearch/theorems/Refutation0.lean](../../equational_theories/Generated/FinSearch/theorems/Refutation0.lean)
- [equational_theories/Generated/FinSearch/theorems/Refutation1.lean](../../equational_theories/Generated/FinSearch/theorems/Refutation1.lean)
- [equational_theories/Generated/FinSearch/theorems/Refutation2.lean](../../equational_theories/Generated/FinSearch/theorems/Refutation2.lean)
- [equational_theories/Generated/FinSearch/theorems/Refutation3.lean](../../equational_theories/Generated/FinSearch/theorems/Refutation3.lean)
- [equational_theories/Generated/FinSearch/theorems/Refutation4.lean](../../equational_theories/Generated/FinSearch/theorems/Refutation4.lean)
- [equational_theories/Generated/FinSearch/theorems/Refutation5.lean](../../equational_theories/Generated/FinSearch/theorems/Refutation5.lean)
- [equational_theories/Generated/FiniteImplicationSearch/theorems/Inverses1.lean](../../equational_theories/Generated/FiniteImplicationSearch/theorems/Inverses1.lean)
- [equational_theories/Generated/FiniteImplicationSearch/theorems/InversesManual.lean](../../equational_theories/Generated/FiniteImplicationSearch/theorems/InversesManual.lean)
- [equational_theories/Generated/FinitePoly/Refutation108.lean](../../equational_theories/Generated/FinitePoly/Refutation108.lean)
- [equational_theories/Generated/FinitePoly/Refutation112.lean](../../equational_theories/Generated/FinitePoly/Refutation112.lean)
- [equational_theories/Generated/FinitePoly/Refutation114.lean](../../equational_theories/Generated/FinitePoly/Refutation114.lean)
- [equational_theories/Generated/FinitePoly/Refutation116.lean](../../equational_theories/Generated/FinitePoly/Refutation116.lean)
- [equational_theories/Generated/FinitePoly/Refutation120.lean](../../equational_theories/Generated/FinitePoly/Refutation120.lean)
- [equational_theories/Generated/FinitePoly/Refutation126.lean](../../equational_theories/Generated/FinitePoly/Refutation126.lean)
- [equational_theories/Generated/FinitePoly/Refutation128.lean](../../equational_theories/Generated/FinitePoly/Refutation128.lean)
- [equational_theories/Generated/FinitePoly/Refutation132.lean](../../equational_theories/Generated/FinitePoly/Refutation132.lean)
- [equational_theories/Generated/FinitePoly/Refutation138.lean](../../equational_theories/Generated/FinitePoly/Refutation138.lean)
- [equational_theories/Generated/FinitePoly/Refutation14.lean](../../equational_theories/Generated/FinitePoly/Refutation14.lean)
- [equational_theories/Generated/FinitePoly/Refutation144.lean](../../equational_theories/Generated/FinitePoly/Refutation144.lean)
- [equational_theories/Generated/FinitePoly/Refutation146.lean](../../equational_theories/Generated/FinitePoly/Refutation146.lean)
- [equational_theories/Generated/FinitePoly/Refutation150.lean](../../equational_theories/Generated/FinitePoly/Refutation150.lean)
- [equational_theories/Generated/FinitePoly/Refutation152.lean](../../equational_theories/Generated/FinitePoly/Refutation152.lean)
- [equational_theories/Generated/FinitePoly/Refutation154.lean](../../equational_theories/Generated/FinitePoly/Refutation154.lean)
- [equational_theories/Generated/FinitePoly/Refutation172.lean](../../equational_theories/Generated/FinitePoly/Refutation172.lean)
- [equational_theories/Generated/FinitePoly/Refutation174.lean](../../equational_theories/Generated/FinitePoly/Refutation174.lean)
- [equational_theories/Generated/FinitePoly/Refutation176.lean](../../equational_theories/Generated/FinitePoly/Refutation176.lean)
- [equational_theories/Generated/FinitePoly/Refutation178.lean](../../equational_theories/Generated/FinitePoly/Refutation178.lean)
- [equational_theories/Generated/FinitePoly/Refutation18.lean](../../equational_theories/Generated/FinitePoly/Refutation18.lean)
- [equational_theories/Generated/FinitePoly/Refutation184.lean](../../equational_theories/Generated/FinitePoly/Refutation184.lean)
- [equational_theories/Generated/FinitePoly/Refutation190.lean](../../equational_theories/Generated/FinitePoly/Refutation190.lean)
- [equational_theories/Generated/FinitePoly/Refutation194.lean](../../equational_theories/Generated/FinitePoly/Refutation194.lean)
- [equational_theories/Generated/FinitePoly/Refutation196.lean](../../equational_theories/Generated/FinitePoly/Refutation196.lean)
- [equational_theories/Generated/FinitePoly/Refutation198.lean](../../equational_theories/Generated/FinitePoly/Refutation198.lean)
- [equational_theories/Generated/FinitePoly/Refutation20.lean](../../equational_theories/Generated/FinitePoly/Refutation20.lean)
- [equational_theories/Generated/FinitePoly/Refutation200.lean](../../equational_theories/Generated/FinitePoly/Refutation200.lean)
- [equational_theories/Generated/FinitePoly/Refutation206.lean](../../equational_theories/Generated/FinitePoly/Refutation206.lean)
- [equational_theories/Generated/FinitePoly/Refutation208.lean](../../equational_theories/Generated/FinitePoly/Refutation208.lean)
- [equational_theories/Generated/FinitePoly/Refutation212.lean](../../equational_theories/Generated/FinitePoly/Refutation212.lean)
- [equational_theories/Generated/FinitePoly/Refutation214.lean](../../equational_theories/Generated/FinitePoly/Refutation214.lean)
- [equational_theories/Generated/FinitePoly/Refutation216.lean](../../equational_theories/Generated/FinitePoly/Refutation216.lean)
- [equational_theories/Generated/FinitePoly/Refutation218.lean](../../equational_theories/Generated/FinitePoly/Refutation218.lean)
- [equational_theories/Generated/FinitePoly/Refutation220.lean](../../equational_theories/Generated/FinitePoly/Refutation220.lean)
- [equational_theories/Generated/FinitePoly/Refutation226.lean](../../equational_theories/Generated/FinitePoly/Refutation226.lean)
- [equational_theories/Generated/FinitePoly/Refutation232.lean](../../equational_theories/Generated/FinitePoly/Refutation232.lean)
- [equational_theories/Generated/FinitePoly/Refutation234.lean](../../equational_theories/Generated/FinitePoly/Refutation234.lean)
- [equational_theories/Generated/FinitePoly/Refutation236.lean](../../equational_theories/Generated/FinitePoly/Refutation236.lean)
- [equational_theories/Generated/FinitePoly/Refutation238.lean](../../equational_theories/Generated/FinitePoly/Refutation238.lean)
- [equational_theories/Generated/FinitePoly/Refutation24.lean](../../equational_theories/Generated/FinitePoly/Refutation24.lean)
- [equational_theories/Generated/FinitePoly/Refutation246.lean](../../equational_theories/Generated/FinitePoly/Refutation246.lean)
- [equational_theories/Generated/FinitePoly/Refutation250.lean](../../equational_theories/Generated/FinitePoly/Refutation250.lean)
- [equational_theories/Generated/FinitePoly/Refutation26.lean](../../equational_theories/Generated/FinitePoly/Refutation26.lean)
- [equational_theories/Generated/FinitePoly/Refutation262.lean](../../equational_theories/Generated/FinitePoly/Refutation262.lean)
- [equational_theories/Generated/FinitePoly/Refutation264.lean](../../equational_theories/Generated/FinitePoly/Refutation264.lean)
- [equational_theories/Generated/FinitePoly/Refutation268.lean](../../equational_theories/Generated/FinitePoly/Refutation268.lean)
- [equational_theories/Generated/FinitePoly/Refutation270.lean](../../equational_theories/Generated/FinitePoly/Refutation270.lean)
- [equational_theories/Generated/FinitePoly/Refutation272.lean](../../equational_theories/Generated/FinitePoly/Refutation272.lean)
- [equational_theories/Generated/FinitePoly/Refutation280.lean](../../equational_theories/Generated/FinitePoly/Refutation280.lean)
- [equational_theories/Generated/FinitePoly/Refutation284.lean](../../equational_theories/Generated/FinitePoly/Refutation284.lean)
- [equational_theories/Generated/FinitePoly/Refutation286.lean](../../equational_theories/Generated/FinitePoly/Refutation286.lean)
- [equational_theories/Generated/FinitePoly/Refutation290.lean](../../equational_theories/Generated/FinitePoly/Refutation290.lean)
- [equational_theories/Generated/FinitePoly/Refutation302.lean](../../equational_theories/Generated/FinitePoly/Refutation302.lean)
- [equational_theories/Generated/FinitePoly/Refutation312.lean](../../equational_theories/Generated/FinitePoly/Refutation312.lean)
- [equational_theories/Generated/FinitePoly/Refutation314.lean](../../equational_theories/Generated/FinitePoly/Refutation314.lean)
- [equational_theories/Generated/FinitePoly/Refutation316.lean](../../equational_theories/Generated/FinitePoly/Refutation316.lean)
- [equational_theories/Generated/FinitePoly/Refutation318.lean](../../equational_theories/Generated/FinitePoly/Refutation318.lean)
- [equational_theories/Generated/FinitePoly/Refutation32.lean](../../equational_theories/Generated/FinitePoly/Refutation32.lean)
- [equational_theories/Generated/FinitePoly/Refutation320.lean](../../equational_theories/Generated/FinitePoly/Refutation320.lean)
- [equational_theories/Generated/FinitePoly/Refutation326.lean](../../equational_theories/Generated/FinitePoly/Refutation326.lean)
- [equational_theories/Generated/FinitePoly/Refutation328.lean](../../equational_theories/Generated/FinitePoly/Refutation328.lean)
- [equational_theories/Generated/FinitePoly/Refutation330.lean](../../equational_theories/Generated/FinitePoly/Refutation330.lean)
- [equational_theories/Generated/FinitePoly/Refutation34.lean](../../equational_theories/Generated/FinitePoly/Refutation34.lean)
- [equational_theories/Generated/FinitePoly/Refutation340.lean](../../equational_theories/Generated/FinitePoly/Refutation340.lean)
- [equational_theories/Generated/FinitePoly/Refutation342.lean](../../equational_theories/Generated/FinitePoly/Refutation342.lean)
- [equational_theories/Generated/FinitePoly/Refutation344.lean](../../equational_theories/Generated/FinitePoly/Refutation344.lean)
- [equational_theories/Generated/FinitePoly/Refutation346.lean](../../equational_theories/Generated/FinitePoly/Refutation346.lean)
- [equational_theories/Generated/FinitePoly/Refutation352.lean](../../equational_theories/Generated/FinitePoly/Refutation352.lean)
- [equational_theories/Generated/FinitePoly/Refutation356.lean](../../equational_theories/Generated/FinitePoly/Refutation356.lean)
- [equational_theories/Generated/FinitePoly/Refutation364.lean](../../equational_theories/Generated/FinitePoly/Refutation364.lean)
- [equational_theories/Generated/FinitePoly/Refutation366.lean](../../equational_theories/Generated/FinitePoly/Refutation366.lean)
- [equational_theories/Generated/FinitePoly/Refutation370.lean](../../equational_theories/Generated/FinitePoly/Refutation370.lean)
- [equational_theories/Generated/FinitePoly/Refutation374.lean](../../equational_theories/Generated/FinitePoly/Refutation374.lean)
- [equational_theories/Generated/FinitePoly/Refutation380.lean](../../equational_theories/Generated/FinitePoly/Refutation380.lean)
- [equational_theories/Generated/FinitePoly/Refutation386.lean](../../equational_theories/Generated/FinitePoly/Refutation386.lean)
- [equational_theories/Generated/FinitePoly/Refutation388.lean](../../equational_theories/Generated/FinitePoly/Refutation388.lean)
- [equational_theories/Generated/FinitePoly/Refutation390.lean](../../equational_theories/Generated/FinitePoly/Refutation390.lean)
- [equational_theories/Generated/FinitePoly/Refutation394.lean](../../equational_theories/Generated/FinitePoly/Refutation394.lean)
- [equational_theories/Generated/FinitePoly/Refutation40.lean](../../equational_theories/Generated/FinitePoly/Refutation40.lean)
- [equational_theories/Generated/FinitePoly/Refutation400.lean](../../equational_theories/Generated/FinitePoly/Refutation400.lean)
- [equational_theories/Generated/FinitePoly/Refutation402.lean](../../equational_theories/Generated/FinitePoly/Refutation402.lean)
- [equational_theories/Generated/FinitePoly/Refutation404.lean](../../equational_theories/Generated/FinitePoly/Refutation404.lean)
- [equational_theories/Generated/FinitePoly/Refutation406.lean](../../equational_theories/Generated/FinitePoly/Refutation406.lean)
- [equational_theories/Generated/FinitePoly/Refutation408.lean](../../equational_theories/Generated/FinitePoly/Refutation408.lean)
- [equational_theories/Generated/FinitePoly/Refutation410.lean](../../equational_theories/Generated/FinitePoly/Refutation410.lean)
- [equational_theories/Generated/FinitePoly/Refutation418.lean](../../equational_theories/Generated/FinitePoly/Refutation418.lean)
- [equational_theories/Generated/FinitePoly/Refutation420.lean](../../equational_theories/Generated/FinitePoly/Refutation420.lean)
- [equational_theories/Generated/FinitePoly/Refutation422.lean](../../equational_theories/Generated/FinitePoly/Refutation422.lean)
- [equational_theories/Generated/FinitePoly/Refutation424.lean](../../equational_theories/Generated/FinitePoly/Refutation424.lean)
- [equational_theories/Generated/FinitePoly/Refutation426.lean](../../equational_theories/Generated/FinitePoly/Refutation426.lean)
- [equational_theories/Generated/FinitePoly/Refutation432.lean](../../equational_theories/Generated/FinitePoly/Refutation432.lean)
- [equational_theories/Generated/FinitePoly/Refutation444.lean](../../equational_theories/Generated/FinitePoly/Refutation444.lean)
- [equational_theories/Generated/FinitePoly/Refutation454.lean](../../equational_theories/Generated/FinitePoly/Refutation454.lean)
- [equational_theories/Generated/FinitePoly/Refutation46.lean](../../equational_theories/Generated/FinitePoly/Refutation46.lean)
- [equational_theories/Generated/FinitePoly/Refutation470.lean](../../equational_theories/Generated/FinitePoly/Refutation470.lean)
- [equational_theories/Generated/FinitePoly/Refutation472.lean](../../equational_theories/Generated/FinitePoly/Refutation472.lean)
- [equational_theories/Generated/FinitePoly/Refutation474.lean](../../equational_theories/Generated/FinitePoly/Refutation474.lean)
- [equational_theories/Generated/FinitePoly/Refutation476.lean](../../equational_theories/Generated/FinitePoly/Refutation476.lean)
- [equational_theories/Generated/FinitePoly/Refutation482.lean](../../equational_theories/Generated/FinitePoly/Refutation482.lean)
- [equational_theories/Generated/FinitePoly/Refutation488.lean](../../equational_theories/Generated/FinitePoly/Refutation488.lean)
- [equational_theories/Generated/FinitePoly/Refutation492.lean](../../equational_theories/Generated/FinitePoly/Refutation492.lean)
- [equational_theories/Generated/FinitePoly/Refutation50.lean](../../equational_theories/Generated/FinitePoly/Refutation50.lean)
- [equational_theories/Generated/FinitePoly/Refutation502.lean](../../equational_theories/Generated/FinitePoly/Refutation502.lean)
- [equational_theories/Generated/FinitePoly/Refutation532.lean](../../equational_theories/Generated/FinitePoly/Refutation532.lean)
- [equational_theories/Generated/FinitePoly/Refutation550.lean](../../equational_theories/Generated/FinitePoly/Refutation550.lean)
- [equational_theories/Generated/FinitePoly/Refutation56.lean](../../equational_theories/Generated/FinitePoly/Refutation56.lean)
- [equational_theories/Generated/FinitePoly/Refutation568.lean](../../equational_theories/Generated/FinitePoly/Refutation568.lean)
- [equational_theories/Generated/FinitePoly/Refutation6.lean](../../equational_theories/Generated/FinitePoly/Refutation6.lean)
- [equational_theories/Generated/FinitePoly/Refutation60.lean](../../equational_theories/Generated/FinitePoly/Refutation60.lean)
- [equational_theories/Generated/FinitePoly/Refutation620.lean](../../equational_theories/Generated/FinitePoly/Refutation620.lean)
- [equational_theories/Generated/FinitePoly/Refutation622.lean](../../equational_theories/Generated/FinitePoly/Refutation622.lean)
- [equational_theories/Generated/FinitePoly/Refutation636.lean](../../equational_theories/Generated/FinitePoly/Refutation636.lean)
- [equational_theories/Generated/FinitePoly/Refutation656.lean](../../equational_theories/Generated/FinitePoly/Refutation656.lean)
- [equational_theories/Generated/FinitePoly/Refutation66.lean](../../equational_theories/Generated/FinitePoly/Refutation66.lean)
- [equational_theories/Generated/FinitePoly/Refutation664.lean](../../equational_theories/Generated/FinitePoly/Refutation664.lean)
- [equational_theories/Generated/FinitePoly/Refutation672.lean](../../equational_theories/Generated/FinitePoly/Refutation672.lean)
- [equational_theories/Generated/FinitePoly/Refutation674.lean](../../equational_theories/Generated/FinitePoly/Refutation674.lean)
- [equational_theories/Generated/FinitePoly/Refutation676.lean](../../equational_theories/Generated/FinitePoly/Refutation676.lean)
- [equational_theories/Generated/FinitePoly/Refutation68.lean](../../equational_theories/Generated/FinitePoly/Refutation68.lean)
- [equational_theories/Generated/FinitePoly/Refutation682.lean](../../equational_theories/Generated/FinitePoly/Refutation682.lean)
- [equational_theories/Generated/FinitePoly/Refutation690.lean](../../equational_theories/Generated/FinitePoly/Refutation690.lean)
- [equational_theories/Generated/FinitePoly/Refutation72.lean](../../equational_theories/Generated/FinitePoly/Refutation72.lean)
- [equational_theories/Generated/FinitePoly/Refutation74.lean](../../equational_theories/Generated/FinitePoly/Refutation74.lean)
- [equational_theories/Generated/FinitePoly/Refutation78.lean](../../equational_theories/Generated/FinitePoly/Refutation78.lean)
- [equational_theories/Generated/FinitePoly/Refutation8.lean](../../equational_theories/Generated/FinitePoly/Refutation8.lean)
- [equational_theories/Generated/FinitePoly/Refutation82.lean](../../equational_theories/Generated/FinitePoly/Refutation82.lean)
- [equational_theories/Generated/FinitePoly/Refutation84.lean](../../equational_theories/Generated/FinitePoly/Refutation84.lean)
- [equational_theories/Generated/FinitePoly/Refutation88.lean](../../equational_theories/Generated/FinitePoly/Refutation88.lean)
- [equational_theories/Generated/FinitePoly/Refutation90.lean](../../equational_theories/Generated/FinitePoly/Refutation90.lean)
- [equational_theories/Generated/FinitePoly/Refutation92.lean](../../equational_theories/Generated/FinitePoly/Refutation92.lean)
- [equational_theories/Generated/FinitePoly/Refutation94.lean](../../equational_theories/Generated/FinitePoly/Refutation94.lean)
- [equational_theories/Generated/FinitePoly/Refutation96.lean](../../equational_theories/Generated/FinitePoly/Refutation96.lean)
- [equational_theories/Generated/Greedy/Eq1112.lean](../../equational_theories/Generated/Greedy/Eq1112.lean)
- [equational_theories/Generated/Greedy/Eq1113.lean](../../equational_theories/Generated/Greedy/Eq1113.lean)
- [equational_theories/Generated/Greedy/Eq118.lean](../../equational_theories/Generated/Greedy/Eq118.lean)
- [equational_theories/Generated/Greedy/Eq124.lean](../../equational_theories/Generated/Greedy/Eq124.lean)
- [equational_theories/Generated/Greedy/Eq1648.lean](../../equational_theories/Generated/Greedy/Eq1648.lean)
- [equational_theories/Generated/Greedy/Eq476.lean](../../equational_theories/Generated/Greedy/Eq476.lean)
- [equational_theories/Generated/Greedy/Eq503.lean](../../equational_theories/Generated/Greedy/Eq503.lean)
- [equational_theories/Generated/Greedy/Eq511.lean](../../equational_theories/Generated/Greedy/Eq511.lean)
- [equational_theories/Generated/Greedy/Eq677.lean](../../equational_theories/Generated/Greedy/Eq677.lean)
- [equational_theories/Generated/Greedy/Eq707.lean](../../equational_theories/Generated/Greedy/Eq707.lean)
- [equational_theories/Generated/Greedy/Eq883.lean](../../equational_theories/Generated/Greedy/Eq883.lean)
- [equational_theories/Generated/Greedy/Eq906.lean](../../equational_theories/Generated/Greedy/Eq906.lean)
- [equational_theories/Generated/InvariantMetatheoremNonimplications/instLiftingMagmaFamilyFinset_counterexamples.lean](../../equational_theories/Generated/InvariantMetatheoremNonimplications/instLiftingMagmaFamilyFinset_counterexamples.lean)
- [equational_theories/Generated/InvariantMetatheoremNonimplications/instLiftingMagmaFamilyLeftProj_counterexamples.lean](../../equational_theories/Generated/InvariantMetatheoremNonimplications/instLiftingMagmaFamilyLeftProj_counterexamples.lean)
- [equational_theories/Generated/InvariantMetatheoremNonimplications/instLiftingMagmaFamilyList_counterexamples.lean](../../equational_theories/Generated/InvariantMetatheoremNonimplications/instLiftingMagmaFamilyList_counterexamples.lean)
- [equational_theories/Generated/InvariantMetatheoremNonimplications/instLiftingMagmaFamilyMultiset_counterexamples.lean](../../equational_theories/Generated/InvariantMetatheoremNonimplications/instLiftingMagmaFamilyMultiset_counterexamples.lean)
- [equational_theories/Generated/InvariantMetatheoremNonimplications/instLiftingMagmaFamilyRightProj_counterexamples.lean](../../equational_theories/Generated/InvariantMetatheoremNonimplications/instLiftingMagmaFamilyRightProj_counterexamples.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wx.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wx.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wy.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wy.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wz.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wz.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wz_yx_zy.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wz_yx_zy.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wz_zx.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wz_zx.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wz_zy.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wz_zy.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_wx.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_wx.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_wz_zy.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_wz_zy.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_ux.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_ux.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_ux_vu.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_ux_vu.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uy.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uy.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uy_vu.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uy_vu.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uz.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uz.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uz_vu.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uz_vu.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vu.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vu.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vw.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vw.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vx.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vx.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vy.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vy.lean)
- [equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vz.lean](../../equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vz.lean)
- [equational_theories/Generated/Singleton.lean](../../equational_theories/Generated/Singleton.lean)
- [equational_theories/Generated/TrivialBruteforce/theorems/Apply2.lean](../../equational_theories/Generated/TrivialBruteforce/theorems/Apply2.lean)
- [equational_theories/Generated/TrivialBruteforce/theorems/RewriteCombinations.lean](../../equational_theories/Generated/TrivialBruteforce/theorems/RewriteCombinations.lean)
- [equational_theories/Generated/TrivialBruteforce/theorems/RewriteGoal.lean](../../equational_theories/Generated/TrivialBruteforce/theorems/RewriteGoal.lean)
- [equational_theories/Generated/TrivialBruteforce/theorems/RewriteHypothesisAndGoal.lean](../../equational_theories/Generated/TrivialBruteforce/theorems/RewriteHypothesisAndGoal.lean)
- [equational_theories/Generated/VampireProven/Proofs3.lean](../../equational_theories/Generated/VampireProven/Proofs3.lean)
- [equational_theories/Generated/Z3GenNonImp.lean](../../equational_theories/Generated/Z3GenNonImp.lean)
- [equational_theories/InfModel.lean](../../equational_theories/InfModel.lean)
- [equational_theories/LinearOps.lean](../../equational_theories/LinearOps.lean)
- [equational_theories/ManuallyProved/Equation1076.lean](../../equational_theories/ManuallyProved/Equation1076.lean)
- [equational_theories/ManuallyProved/Equation1117.lean](../../equational_theories/ManuallyProved/Equation1117.lean)
- [equational_theories/ManuallyProved/Equation1133.lean](../../equational_theories/ManuallyProved/Equation1133.lean)
- [equational_theories/ManuallyProved/Equation1289.lean](../../equational_theories/ManuallyProved/Equation1289.lean)
- [equational_theories/ManuallyProved/Equation1323.lean](../../equational_theories/ManuallyProved/Equation1323.lean)
- [equational_theories/ManuallyProved/Equation1437.lean](../../equational_theories/ManuallyProved/Equation1437.lean)
- [equational_theories/ManuallyProved/Equation1441.lean](../../equational_theories/ManuallyProved/Equation1441.lean)
- [equational_theories/ManuallyProved/Equation1447.lean](../../equational_theories/ManuallyProved/Equation1447.lean)
- [equational_theories/ManuallyProved/Equation1516.lean](../../equational_theories/ManuallyProved/Equation1516.lean)
- [equational_theories/ManuallyProved/Equation1518.lean](../../equational_theories/ManuallyProved/Equation1518.lean)
- [equational_theories/ManuallyProved/Equation1526.lean](../../equational_theories/ManuallyProved/Equation1526.lean)
- [equational_theories/ManuallyProved/Equation1648.lean](../../equational_theories/ManuallyProved/Equation1648.lean)
- [equational_theories/ManuallyProved/Equation1659.lean](../../equational_theories/ManuallyProved/Equation1659.lean)
- [equational_theories/ManuallyProved/Equation1661.lean](../../equational_theories/ManuallyProved/Equation1661.lean)
- [equational_theories/ManuallyProved/Equation1692.lean](../../equational_theories/ManuallyProved/Equation1692.lean)
- [equational_theories/ManuallyProved/Equation1701.lean](../../equational_theories/ManuallyProved/Equation1701.lean)
- [equational_theories/ManuallyProved/Equation1722.lean](../../equational_theories/ManuallyProved/Equation1722.lean)
- [equational_theories/ManuallyProved/Equation1729.lean](../../equational_theories/ManuallyProved/Equation1729.lean)
- [equational_theories/ManuallyProved/Equation3308.lean](../../equational_theories/ManuallyProved/Equation3308.lean)
- [equational_theories/ManuallyProved/Equation3342.lean](../../equational_theories/ManuallyProved/Equation3342.lean)
- [equational_theories/ManuallyProved/Equation467.lean](../../equational_theories/ManuallyProved/Equation467.lean)
- [equational_theories/ManuallyProved/Equation63.lean](../../equational_theories/ManuallyProved/Equation63.lean)
- [equational_theories/ManuallyProved/Equation713.lean](../../equational_theories/ManuallyProved/Equation713.lean)
- [equational_theories/ManuallyProved/Equation73.lean](../../equational_theories/ManuallyProved/Equation73.lean)
- [equational_theories/ManuallyProved/Equation854.lean](../../equational_theories/ManuallyProved/Equation854.lean)
- [equational_theories/ManuallyProved/Equation906.lean](../../equational_theories/ManuallyProved/Equation906.lean)
- [equational_theories/ManuallyProved/Equation917.lean](../../equational_theories/ManuallyProved/Equation917.lean)
- [equational_theories/Obelix.lean](../../equational_theories/Obelix.lean)
- [equational_theories/Sheffer.lean](../../equational_theories/Sheffer.lean)
- [equational_theories/SmallMagmas.lean](../../equational_theories/SmallMagmas.lean)
- [equational_theories/StringMagmas.lean](../../equational_theories/StringMagmas.lean)
- [equational_theories/Subgraph.lean](../../equational_theories/Subgraph.lean)
- [equational_theories/ThreeC2.lean](../../equational_theories/ThreeC2.lean)
- [equational_theories/Z3Counterexamples.lean](../../equational_theories/Z3Counterexamples.lean)

### Skipped conjectures

Conjecture declarations are not used as proof seeds.

| Source | Statement |
|---|---|
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation467_not_implies_Equation2847 : ∃ (G : Type) (_ : Magma G), Equation467 G ∧ ¬Equation2847 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation477_not_implies_Equation1426 : ∃ (G : Type) (_ : Magma G), Equation477 G ∧ ¬Equation1426 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation477_not_implies_Equation1519 : ∃ (G : Type) (_ : Magma G), Equation477 G ∧ ¬Equation1519 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation477_not_implies_Equation2035 : ∃ (G : Type) (_ : Magma G), Equation477 G ∧ ¬Equation2035 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation477_not_implies_Equation2128 : ∃ (G : Type) (_ : Magma G), Equation477 G ∧ ¬Equation2128 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation477_not_implies_Equation3050 : ∃ (G : Type) (_ : Magma G), Equation477 G ∧ ¬Equation3050 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation477_not_implies_Equation3150 : ∃ (G : Type) (_ : Magma G), Equation477 G ∧ ¬Equation3150 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation504_not_implies_Equation817 : ∃ (G : Type) (_ : Magma G), Equation504 G ∧ ¬Equation817 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation504_not_implies_Equation1629 : ∃ (G : Type) (_ : Magma G), Equation504 G ∧ ¬Equation1629 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation504_not_implies_Equation1832 : ∃ (G : Type) (_ : Magma G), Equation504 G ∧ ¬Equation1832 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation504_not_implies_Equation1925 : ∃ (G : Type) (_ : Magma G), Equation504 G ∧ ¬Equation1925 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation1515_not_implies_Equation4590 : ∃ (G : Type) (_ : Magma G), Equation1515 G ∧ ¬Equation4590 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation2038_not_implies_Equation4270 : ∃ (G : Type) (_ : Magma G), Equation2038 G ∧ ¬Equation4270 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation3140_not_implies_Equation614 : ∃ (G : Type) (_ : Magma G), Equation3140 G ∧ ¬Equation614 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation3143_not_implies_Equation1629 : ∃ (G : Type) (_ : Magma G), Equation3143 G ∧ ¬Equation1629 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation3143_not_implies_Equation1832 : ∃ (G : Type) (_ : Magma G), Equation3143 G ∧ ¬Equation1832 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation3143_not_implies_Equation2644 : ∃ (G : Type) (_ : Magma G), Equation3143 G ∧ ¬Equation2644 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation3150_not_implies_Equation411 : ∃ (G : Type) (_ : Magma G), Equation3150 G ∧ ¬Equation411 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation3150_not_implies_Equation1426 : ∃ (G : Type) (_ : Magma G), Equation3150 G ∧ ¬Equation1426 G` |
| [ManuallySampled.lean](../../equational_theories/Generated/Confluence/ManuallySampled.lean) | `conjecture Equation3150_not_implies_Equation2035 : ∃ (G : Type) (_ : Magma G), Equation3150 G ∧ ¬Equation2035 G end Confluence` |
| [Equation1516.lean](../../equational_theories/ManuallyProved/Equation1516.lean) | `conjecture Equation1516_facts : ∃ (G : Type) (_ : Magma G), Facts G [1516] [255] end Eq1516` |
| [Sheffer.lean](../../equational_theories/Sheffer.lean) | `conjecture Equation321577_implies_Equation329857 (G: Type*) [Magma G] (_ : Equation321577 G) : Equation329857 G` |
| [Sheffer.lean](../../equational_theories/Sheffer.lean) | `conjecture Equation321577_implies_Equation345169 (G: Type*) [Magma G] (_ : Equation321577 G) : Equation345169 G` |
| [Sheffer.lean](../../equational_theories/Sheffer.lean) | `conjecture Equatio321577_implies_Equation361729 (G: Type*) [Magma G] (_ : Equation321577 G) : Equation361729 G` |
| [Sheffer.lean](../../equational_theories/Sheffer.lean) | `conjecture Equation329857_implies_Equation321577 (G: Type*) [Magma G] (_ : Equation329857 G) : Equation321577 G` |
| [Sheffer.lean](../../equational_theories/Sheffer.lean) | `conjecture Equation345169_implies_Equation321577 (G: Type*) [Magma G] (_ : Equation345169 G) : Equation321577 G` |
| [Sheffer.lean](../../equational_theories/Sheffer.lean) | `conjecture Equation361729_implies_Equation321577 (G: Type*) [Magma G] (_ : Equation361729 G) : Equation321577 G end Sheffer` |

## Definability scan

12,893 positive and 136,044 negative fact occurrences; 135,565 negative occurrences seed the finite flavour.

4 universal rows; 1 universal columns; 287 paired certificate families; 13,655 reachable local modules.

Orphan declarations: `[]`.

Unpaired Satisfies families: `['negInt']`.

Unpaired FamilyRefutes families: `[]`.

Unclassified carrier strings (including appearances in positive proofs): `['(FixedPointCycle.A 2)', '(FixedPointCycle.A 3)', '(FixedPointCycle.A 4)', '(FixedPointCycle.A 5)', '(FixedPointsOrbit.A (Fin 2)', '(FreeOrbit.A 2 2)', '(V 2)', '(V 3)', 'G', 'G)', 'G,', 'GaussianInt', 'NEFinsetInt', 'R', '_']`.

Refutations with no recognized carrier: 163; with mixed carrier classifications: 0.

### All negative declarations with carrier warnings

`FromFin` independently certifies the finite flavour even without a parsed carrier.
“Finite seed” records how the parser classified this occurrence; “finite closure”
records whether the finite negative is known after all propagation. A missing
finite seed is not automatically an open cell or an error.

| Declaration | Carrier strings | Source → target / relation | Finite seed | Finite closure |
|---|---|---|---|---|
| [Equation167_not_definableFromFin_Equation1486_spectrum](../../equational_theories/Definability/CentralSpectrum.lean) | `[]` | 1486 → 167 / definable | True | True |
| [Equation168_not_definableFromFin_Equation1486_spectrum](../../equational_theories/Definability/CentralSpectrum.lean) | `[]` | 1486 → 168 / definable | True | True |
| [Equation1485_not_definableFromFin_Equation1486_spectrum](../../equational_theories/Definability/CentralSpectrum.lean) | `[]` | 1486 → 1485 / definable | True | True |
| [Equation1483_not_definableFromFin_Equation1486_spectrum](../../equational_theories/Definability/CentralSpectrum.lean) | `[]` | 1486 → 1483 / definable | True | True |
| [Equation1113_not_termStructuralFrom_Equation1496_gaussian](../../equational_theories/Definability/GaussianRecovery.lean) | `['GaussianInt']` | 1496 → 1113 / termStructural | False | False |
| [Equation680_not_termStructuralFrom_Equation1496_gaussian](../../equational_theories/Definability/GaussianRecovery.lean) | `['GaussianInt']` | 1496 → 680 / termStructural | False | True |
| [Equation1682_not_termStructuralFrom_Equation1496_gaussian](../../equational_theories/Definability/GaussianRecovery.lean) | `['GaussianInt']` | 1496 → 1682 / termStructural | False | False |
| [Equation1045_not_termStructuralFromFin_Equation1632_congruenceMatrix](../../equational_theories/Definability/Generated/CongruenceMatrixNegative.lean) | `[]` | 1632 → 1045 / termStructural | True | True |
| [Equation667_not_termStructuralFromFin_Equation898_deepMatrixCount](../../equational_theories/Definability/Generated/DeepMatrixCount0.lean) | `[]` | 898 → 667 / termStructural | True | True |
| [Equation642_not_termStructuralFromFin_Equation690_deepMatrixCount](../../equational_theories/Definability/Generated/DeepMatrixCount1.lean) | `[]` | 690 → 642 / termStructural | True | True |
| [Equation55_not_termStructuralFromFin_Equation690_deepMatrixCount](../../equational_theories/Definability/Generated/DeepMatrixCount1.lean) | `[]` | 690 → 55 / termStructural | True | True |
| [Equation632_not_termStructuralFromFin_Equation690_deepMatrixCount](../../equational_theories/Definability/Generated/DeepMatrixCount1.lean) | `[]` | 690 → 632 / termStructural | True | True |
| [Equation4268_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount0.lean) | `['(FixedPointCycle.A 5)']` | 420 → 4268 / termStructural | True | True |
| [Equation3459_not_termStructuralFromFin_Equation56_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount0.lean) | `['(FixedPointCycle.A 5)']` | 56 → 3459 / termStructural | True | True |
| [Equation1023_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount0.lean) | `['(FixedPointCycle.A 5)']` | 420 → 1023 / termStructural | True | True |
| [Equation3318_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount0.lean) | `['(FixedPointCycle.A 5)']` | 420 → 3318 / termStructural | True | True |
| [Equation1637_not_termStructuralFromFin_Equation440_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount0.lean) | `['(FixedPointCycle.A 5)']` | 440 → 1637 / termStructural | True | True |
| [Equation620_not_termStructuralFromFin_Equation1050_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount0.lean) | `['(FixedPointCycle.A 5)']` | 1050 → 620 / termStructural | True | True |
| [Equation3462_not_termStructuralFromFin_Equation1050_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount0.lean) | `['(FixedPointCycle.A 5)']` | 1050 → 3462 / termStructural | True | True |
| [Equation3459_not_termStructuralFromFin_Equation1435_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount0.lean) | `['(FixedPointCycle.A 5)']` | 1435 → 3459 / termStructural | True | True |
| [Equation1023_not_termStructuralFromFin_Equation56_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount1.lean) | `['(FixedPointCycle.A 5)']` | 56 → 1023 / termStructural | True | True |
| [Equation413_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount1.lean) | `['(FixedPointCycle.A 5)']` | 420 → 413 / termStructural | True | True |
| [Equation1634_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount1.lean) | `['(FixedPointCycle.A 5)']` | 420 → 1634 / termStructural | True | True |
| [Equation3457_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount1.lean) | `['(FixedPointCycle.A 5)']` | 420 → 3457 / termStructural | True | True |
| [Equation1023_not_termStructuralFromFin_Equation623_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount1.lean) | `['(FixedPointCycle.A 5)']` | 623 → 1023 / termStructural | True | True |
| [Equation1053_not_termStructuralFromFin_Equation1050_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount1.lean) | `['(FixedPointCycle.A 5)']` | 1050 → 1053 / termStructural | True | True |
| [Equation845_not_termStructuralFromFin_Equation1253_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount1.lean) | `['(FixedPointCycle.A 5)']` | 1253 → 845 / termStructural | True | True |
| [Equation3261_not_termStructuralFromFin_Equation1638_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount1.lean) | `['(FixedPointCycle.A 5)']` | 1638 → 3261 / termStructural | True | True |
| [Equation1045_not_termStructuralFromFin_Equation56_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount2.lean) | `['(FixedPointCycle.A 5)']` | 56 → 1045 / termStructural | True | True |
| [Equation416_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount2.lean) | `['(FixedPointCycle.A 5)']` | 420 → 416 / termStructural | True | True |
| [Equation1691_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount2.lean) | `['(FixedPointCycle.A 5)']` | 420 → 1691 / termStructural | True | True |
| [Equation3512_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount2.lean) | `['(FixedPointCycle.A 5)']` | 420 → 3512 / termStructural | True | True |
| [Equation620_not_termStructuralFromFin_Equation624_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount2.lean) | `['(FixedPointCycle.A 5)']` | 624 → 620 / termStructural | True | True |
| [Equation1267_not_termStructuralFromFin_Equation1050_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount2.lean) | `['(FixedPointCycle.A 5)']` | 1050 → 1267 / termStructural | True | True |
| [Equation843_not_termStructuralFromFin_Equation1255_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount2.lean) | `['(FixedPointCycle.A 5)']` | 1255 → 843 / termStructural | True | True |
| [Equation3459_not_termStructuralFromFin_Equation1638_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount2.lean) | `['(FixedPointCycle.A 5)']` | 1638 → 3459 / termStructural | True | True |
| [Equation3261_not_termStructuralFromFin_Equation56_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount3.lean) | `['(FixedPointCycle.A 5)']` | 56 → 3261 / termStructural | True | True |
| [Equation419_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount3.lean) | `['(FixedPointCycle.A 5)']` | 420 → 419 / termStructural | True | True |
| [Equation3254_not_termStructuralFromFin_Equation420_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount3.lean) | `['(FixedPointCycle.A 5)']` | 420 → 3254 / termStructural | True | True |
| [Equation436_not_termStructuralFromFin_Equation440_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount3.lean) | `['(FixedPointCycle.A 5)']` | 440 → 436 / termStructural | True | True |
| [Equation3320_not_termStructuralFromFin_Equation626_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount3.lean) | `['(FixedPointCycle.A 5)']` | 626 → 3320 / termStructural | True | True |
| [Equation1635_not_termStructuralFromFin_Equation1050_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount3.lean) | `['(FixedPointCycle.A 5)']` | 1050 → 1635 / termStructural | True | True |
| [Equation3261_not_termStructuralFromFin_Equation1435_extendedSymmetryCount](../../equational_theories/Definability/Generated/ExtendedSymmetryCount3.lean) | `['(FixedPointCycle.A 5)']` | 1435 → 3261 / termStructural | True | True |
| [Equation3318_not_termStructuralFromFin_Equation618_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCount11Index5.lean) | `[]` | 618 → 3318 / termStructural | True | True |
| [Equation1022_not_termStructuralFromFin_Equation48_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCount13Index4.lean) | `[]` | 48 → 1022 / termStructural | True | True |
| [Equation3254_not_termStructuralFromFin_Equation412_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCount13Index4.lean) | `[]` | 412 → 3254 / termStructural | True | True |
| [Equation1027_not_termStructuralFromFin_Equation1235_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCyclic16Power1.lean) | `[]` | 1235 → 1027 / termStructural | True | True |
| [Equation4275_not_termStructuralFromFin_Equation1525_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCyclic9Power2.lean) | `[]` | 1525 → 4275 / termStructural | True | True |
| [Equation3537_not_termStructuralFromFin_Equation1469_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCyclic9Power3.lean) | `[]` | 1469 → 3537 / termStructural | True | True |
| [Equation4287_not_termStructuralFromFin_Equation162_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCyclic9Power3.lean) | `[]` | 162 → 4287 / termStructural | True | True |
| [Equation4287_not_termStructuralFromFin_Equation1461_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCyclic9Power3.lean) | `[]` | 1461 → 4287 / termStructural | True | True |
| [Equation4287_not_termStructuralFromFin_Equation1469_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCyclic9Power3.lean) | `[]` | 1469 → 4287 / termStructural | True | True |
| [Equation3264_not_termStructuralFromFin_Equation450_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCyclic9Power3.lean) | `[]` | 450 → 3264 / termStructural | True | True |
| [Equation1457_not_termStructuralFromFin_Equation1469_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantCyclic9Power3.lean) | `[]` | 1469 → 1457 / termStructural | True | True |
| [Equation100_not_termStructuralFromFin_Equation1250_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianAugmentedAffine11Index1Fixed2Symmetric0.lean) | `[]` | 1250 → 100 / termStructural | True | True |
| [Equation1234_not_termStructuralFromFin_Equation111_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianAugmentedAffine11Index2Fixed1Symmetric0.lean) | `[]` | 111 → 1234 / termStructural | True | True |
| [Equation105_not_termStructuralFromFin_Equation1052_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianAugmentedAffine23Index2Fixed1Symmetric0.lean) | `[]` | 1052 → 105 / termStructural | True | True |
| [Equation1039_not_termStructuralFromFin_Equation1052_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianAugmentedAffine7Index2Fixed1Symmetric0.lean) | `[]` | 1052 → 1039 / termStructural | True | True |
| [Equation1234_not_termStructuralFromFin_Equation1230_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianAugmentedAffine7Index2Fixed1Symmetric0.lean) | `[]` | 1230 → 1234 / termStructural | True | True |
| [Equation1032_not_termStructuralFromFin_Equation1235_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianAugmentedAffine7Index3Fixed1Symmetric0.lean) | `[]` | 1235 → 1032 / termStructural | True | True |
| [Equation3521_not_termStructuralFromFin_Equation1445_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianCppAugmentedAffine13Index3Fixed2Symmetric0.lean) | `[]` | 1445 → 3521 / termStructural | True | True |
| [Equation828_not_termStructuralFromFin_Equation1033_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianCppAugmentedAffine29Index4Fixed1Symmetric0.lean) | `[]` | 1033 → 828 / termStructural | True | True |
| [Equation1227_not_termStructuralFromFin_Equation1033_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianCyclic33Subgroup1248161725293132.lean) | `[]` | 1033 → 1227 / termStructural | True | True |
| [Equation1633_not_termStructuralFromFin_Equation1033_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianCyclic33Subgroup1248161725293132.lean) | `[]` | 1033 → 1633 / termStructural | True | True |
| [Equation3460_not_termStructuralFromFin_Equation1033_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianCyclic33Subgroup1248161725293132.lean) | `[]` | 1033 → 3460 / termStructural | True | True |
| [Equation829_not_termStructuralFromFin_Equation1033_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianCyclic39Subgroup1245810111620222532.lean) | `[]` | 1033 → 829 / termStructural | True | True |
| [Equation3259_not_termStructuralFromFin_Equation1432_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianCyclic8Subgroup1And3.lean) | `[]` | 1432 → 3259 / termStructural | True | True |
| [Equation323_not_termStructuralFromFin_Equation1441_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianHeisenberg3D2Tri1Shift1.lean) | `[]` | 1441 → 323 / termStructural | True | True |
| [Equation3334_not_termStructuralFromFin_Equation162_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianMatrixrepSymmetric23By3General.lean) | `[]` | 162 → 3334 / termStructural | True | True |
| [Equation3334_not_termStructuralFromFin_Equation1461_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianMatrixrepSymmetric23By3General.lean) | `[]` | 1461 → 3334 / termStructural | True | True |
| [Equation3334_not_termStructuralFromFin_Equation1469_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianMatrixrepSymmetric23By3General.lean) | `[]` | 1469 → 3334 / termStructural | True | True |
| [Equation827_not_termStructuralFromFin_Equation1235_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect25By4Q7A1B1.lean) | `[]` | 1235 → 827 / termStructural | True | True |
| [Equation3264_not_termStructuralFromFin_Equation58_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By3Q2A1B7.lean) | `[]` | 58 → 3264 / termStructural | True | True |
| [Equation1021_not_termStructuralFromFin_Equation418_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By3Q2A1B7.lean) | `[]` | 418 → 1021 / termStructural | True | True |
| [Equation1701_not_termStructuralFromFin_Equation418_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By3Q2A1B7.lean) | `[]` | 418 → 1701 / termStructural | True | True |
| [Equation3264_not_termStructuralFromFin_Equation1437_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By3Q2A1B7.lean) | `[]` | 1437 → 3264 / termStructural | True | True |
| [Equation3526_not_termStructuralFromFin_Equation1525_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By3Q2A1B7.lean) | `[]` | 1525 → 3526 / termStructural | True | True |
| [Equation4268_not_termStructuralFromFin_Equation418_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By6Q3A1B1.lean) | `[]` | 418 → 4268 / termStructural | True | True |
| [Equation820_not_termStructuralFromFin_Equation418_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By6Q3A1B1.lean) | `[]` | 418 → 820 / termStructural | True | True |
| [Equation3256_not_termStructuralFromFin_Equation418_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By6Q3A1B1.lean) | `[]` | 418 → 3256 / termStructural | True | True |
| [Equation3457_not_termStructuralFromFin_Equation418_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By6Q3A1B1.lean) | `[]` | 418 → 3457 / termStructural | True | True |
| [Equation823_not_termStructuralFromFin_Equation418_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By6Q3A1B1.lean) | `[]` | 418 → 823 / termStructural | True | True |
| [Equation1224_not_termStructuralFromFin_Equation418_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By6Q3A1B1.lean) | `[]` | 418 → 1224 / termStructural | True | True |
| [Equation1478_not_termStructuralFromFin_Equation418_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSemidirect7By6Q3A1B1.lean) | `[]` | 418 → 1478 / termStructural | True | True |
| [Equation872_not_termStructuralFromFin_Equation1518_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSetactionTuples3Choose2Symmetric.lean) | `[]` | 1518 → 872 / termStructural | True | True |
| [Equation72_not_termStructuralFromFin_Equation916_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSetactionTuples3Choose2Symmetric.lean) | `[]` | 916 → 72 / termStructural | True | True |
| [Equation1525_not_termStructuralFromFin_Equation916_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSetactionTuples3Choose2Symmetric.lean) | `[]` | 916 → 1525 / termStructural | True | True |
| [Equation4269_not_termStructuralFromFin_Equation1441_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSetactionTuples3Choose2Symmetric.lean) | `[]` | 1441 → 4269 / termStructural | True | True |
| [Equation679_not_termStructuralFromFin_Equation1518_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSetactionTuples3Choose2Symmetric.lean) | `[]` | 1518 → 679 / termStructural | True | True |
| [Equation3459_not_termStructuralFromFin_Equation1632_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSetactionTuples5Choose2Symmetric.lean) | `[]` | 1632 → 3459 / termStructural | True | True |
| [Equation1122_not_termStructuralFromFin_Equation1645_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSetactionTuples6Choose2Symmetric.lean) | `[]` | 1645 → 1122 / termStructural | True | True |
| [Equation1731_not_termStructuralFromFin_Equation1645_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSetactionTuples6Choose2Symmetric.lean) | `[]` | 1645 → 1731 / termStructural | True | True |
| [Equation3278_not_termStructuralFromFin_Equation1645_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantNonabelianSetactionTuples6Choose2Symmetric.lean) | `[]` | 1645 → 3278 / termStructural | True | True |
| [Equation1259_not_termStructuralFromFin_Equation1245_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectiveFanoDualityFixed1.lean) | `[]` | 1245 → 1259 / termStructural | True | True |
| [Equation1032_not_termStructuralFromFin_Equation1033_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectiveFanoFlagsFixed1.lean) | `[]` | 1033 → 1032 / termStructural | True | True |
| [Equation1239_not_termStructuralFromFin_Equation1050_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectiveLine5PairsSLFixed1.lean) | `[]` | 1050 → 1239 / termStructural | True | True |
| [Equation1248_not_termStructuralFromFin_Equation1252_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectiveLine5PairsSLFixed1.lean) | `[]` | 1252 → 1248 / termStructural | True | True |
| [Equation1225_not_termStructuralFromFin_Equation1253_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectiveLine5PairsSLFixed1.lean) | `[]` | 1253 → 1225 / termStructural | True | True |
| [Equation1227_not_termStructuralFromFin_Equation1255_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectiveLine5PairsSLFixed1.lean) | `[]` | 1255 → 1227 / termStructural | True | True |
| [Equation1109_not_termStructuralFromFin_Equation1322_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectiveLine5Triples.lean) | `[]` | 1322 → 1109 / termStructural | True | True |
| [Equation3259_not_termStructuralFromFin_Equation1050_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectiveLine5TriplesFixed1.lean) | `[]` | 1050 → 3259 / termStructural | True | True |
| [Equation819_not_termStructuralFromFin_Equation1253_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectiveLine5TriplesFixed1.lean) | `[]` | 1253 → 819 / termStructural | True | True |
| [Equation824_not_termStructuralFromFin_Equation1033_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectivePlane3FlagsFixed1.lean) | `[]` | 1033 → 824 / termStructural | True | True |
| [Equation1236_not_termStructuralFromFin_Equation1233_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantProjectivePlane3Nonflags.lean) | `[]` | 1233 → 1236 / termStructural | True | True |
| [Equation1461_not_termStructuralFromFin_Equation1469_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantRing2Degree3TruncatedPower2.lean) | `[]` | 1469 → 1461 / termStructural | True | True |
| [Equation3515_not_termStructuralFromFin_Equation1469_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantRing2Degree3TruncatedPower2.lean) | `[]` | 1469 → 3515 / termStructural | True | True |
| [Equation4269_not_termStructuralFromFin_Equation1650_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantRing2Degree3TruncatedPower2.lean) | `[]` | 1650 → 4269 / termStructural | True | True |
| [Equation616_not_termStructuralFromFin_Equation48_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantRing7Degree2TruncatedPower2.lean) | `[]` | 48 → 616 / termStructural | True | True |
| [Equation818_not_termStructuralFromFin_Equation1253_invariantFamilyCount](../../equational_theories/Definability/Generated/InvariantSymplectic3NonisotropicPlanesFixed1.lean) | `[]` | 1253 → 818 / termStructural | True | True |
| [Equation3253_not_termStructuralFromFin_Equation500_largerTruncatedCount](../../equational_theories/Definability/Generated/LargerTruncatedCount0.lean) | `[]` | 500 → 3253 / termStructural | True | True |
| [Equation3253_not_termStructuralFromFin_Equation1122_largerTruncatedCount](../../equational_theories/Definability/Generated/LargerTruncatedCount1.lean) | `[]` | 1122 → 3253 / termStructural | True | True |
| [Equation3253_not_termStructuralFromFin_Equation1731_largerTruncatedCount](../../equational_theories/Definability/Generated/LargerTruncatedCount1.lean) | `[]` | 1731 → 3253 / termStructural | True | True |
| [Equation1637_not_termStructuralFromFin_Equation643_largerTruncatedCount](../../equational_theories/Definability/Generated/LargerTruncatedCount2.lean) | `[]` | 643 → 1637 / termStructural | True | True |
| [Equation3712_not_termStructuralFromFin_Equation643_largerTruncatedCount](../../equational_theories/Definability/Generated/LargerTruncatedCount2.lean) | `[]` | 643 → 3712 / termStructural | True | True |
| [Equation3721_not_termStructuralFromFin_Equation643_largerTruncatedCount](../../equational_theories/Definability/Generated/LargerTruncatedCount2.lean) | `[]` | 643 → 3721 / termStructural | True | True |
| [Equation1027_not_termStructuralFromFin_Equation1033_leftProjectionA4AutomorphismBy2](../../equational_theories/Definability/Generated/LeftProjectionA4AutomorphismBy2.lean) | `[]` | 1033 → 1027 / termStructural | True | True |
| [Equation621_not_termStructuralFromFin_Equation418_leftProjectionS3By2](../../equational_theories/Definability/Generated/LeftProjectionS3By2.lean) | `[]` | 418 → 621 / termStructural | True | True |
| [Equation11_not_termStructuralFromFin_Equation861_matrixAffineCount](../../equational_theories/Definability/Generated/MatrixAffineCount.lean) | `['(V 2)']` | 861 → 11 / termStructural | True | True |
| [Equation630_not_termStructuralFromFin_Equation861_matrixAffineCount](../../equational_theories/Definability/Generated/MatrixAffineCount.lean) | `['(V 2)']` | 861 → 630 / termStructural | True | True |
| [Equation643_not_termStructuralFromFin_Equation861_matrixAffineCount](../../equational_theories/Definability/Generated/MatrixAffineCount.lean) | `['(V 2)']` | 861 → 643 / termStructural | True | True |
| [Equation658_not_termStructuralFromFin_Equation861_matrixAffineCount](../../equational_theories/Definability/Generated/MatrixAffineCount.lean) | `['(V 2)']` | 861 → 658 / termStructural | True | True |
| [Equation820_not_termStructuralFromFin_Equation861_matrixAffineCount](../../equational_theories/Definability/Generated/MatrixAffineCount.lean) | `['(V 2)']` | 861 → 820 / termStructural | True | True |
| [Equation1252_not_termStructuralFromFin_Equation861_matrixAffineCount](../../equational_theories/Definability/Generated/MatrixAffineCount.lean) | `['(V 2)']` | 861 → 1252 / termStructural | True | True |
| [Equation1256_not_termStructuralFromFin_Equation861_matrixAffineCount](../../equational_theories/Definability/Generated/MatrixAffineCount.lean) | `['(V 2)']` | 861 → 1256 / termStructural | True | True |
| [Equation16_not_termStructuralFromFin_Equation1184_matrixAffineCount](../../equational_theories/Definability/Generated/MatrixAffineCount.lean) | `['(V 2)']` | 1184 → 16 / termStructural | True | True |
| [Equation1691_not_termStructuralFromFin_Equation1184_matrixAffineCount](../../equational_theories/Definability/Generated/MatrixAffineCount.lean) | `['(V 2)']` | 1184 → 1691 / termStructural | True | True |
| [Equation1239_not_termStructuralFromFin_Equation633_matrixAffineCount](../../equational_theories/Definability/Generated/MatrixAffineCount.lean) | `['(V 3)']` | 633 → 1239 / termStructural | True | True |
| [Equation1026_not_termStructuralFromFin_Equation1233_monoidCyclic16Times4Units](../../equational_theories/Definability/Generated/MonoidCyclic16Times4Units.lean) | `[]` | 1233 → 1026 / termStructural | True | True |
| [Equation828_not_termStructuralFromFin_Equation1235_monoidCyclic16Times4Units](../../equational_theories/Definability/Generated/MonoidCyclic16Times4Units.lean) | `[]` | 1235 → 828 / termStructural | True | True |
| [Equation1026_not_termStructuralFromFin_Equation1235_monoidCyclic16Times4Units](../../equational_theories/Definability/Generated/MonoidCyclic16Times4Units.lean) | `[]` | 1235 → 1026 / termStructural | True | True |
| [Equation1026_not_termStructuralFromFin_Equation1236_monoidCyclic16Times4Units](../../equational_theories/Definability/Generated/MonoidCyclic16Times4Units.lean) | `[]` | 1236 → 1026 / termStructural | True | True |
| [Equation422_not_termStructuralFromFin_Equation418_monoidCyclic9Times3](../../equational_theories/Definability/Generated/MonoidCyclic9Times3.lean) | `[]` | 418 → 422 / termStructural | True | True |
| [Equation618_not_termStructuralFromFin_Equation418_monoidCyclic9Times3](../../equational_theories/Definability/Generated/MonoidCyclic9Times3.lean) | `[]` | 418 → 618 / termStructural | True | True |
| [Equation3458_not_termStructuralFromFin_Equation1055_monoidDihedral8](../../equational_theories/Definability/Generated/MonoidDihedral8.lean) | `[]` | 1055 → 3458 / termStructural | True | True |
| [Equation3318_not_termStructuralFromFin_Equation827_projectionBase4By5Actions13And1234](../../equational_theories/Definability/Generated/ProjectionBase4By5Actions13And1234.lean) | `[]` | 827 → 3318 / termStructural | True | True |
| [Equation3521_not_termStructuralFromFin_Equation1443_projectionBase4By5Actions13And14](../../equational_theories/Definability/Generated/ProjectionBase4By5Actions13And14.lean) | `[]` | 1443 → 3521 / termStructural | True | True |
| [Equation4314_not_termStructuralFromFin_Equation1443_projectionBase4By5Actions13And14](../../equational_theories/Definability/Generated/ProjectionBase4By5Actions13And14.lean) | `[]` | 1443 → 4314 / termStructural | True | True |
| [Equation819_not_termStructuralFromFin_Equation49_projectionGroupCount10](../../equational_theories/Definability/Generated/ProjectionGroupCount10.lean) | `[]` | 49 → 819 / termStructural | True | True |
| [Equation3264_not_termStructuralFromFin_Equation446_projectionGroupCount12Cyclic](../../equational_theories/Definability/Generated/ProjectionGroupCount12Cyclic.lean) | `[]` | 446 → 3264 / termStructural | True | True |
| [Equation117_not_termStructuralFromFin_Equation1353_projectionGroupCount8](../../equational_theories/Definability/Generated/ProjectionGroupCount8.lean) | `[]` | 1353 → 117 / termStructural | True | True |
| [Equation3518_not_termStructuralFromFin_Equation1353_projectionGroupCount8](../../equational_theories/Definability/Generated/ProjectionGroupCount8.lean) | `[]` | 1353 → 3518 / termStructural | True | True |
| [Equation1109_not_termStructuralFromFin_Equation124_projectionKernel2By17Scalars12489131516](../../equational_theories/Definability/Generated/ProjectionKernel2By17Scalars12489131516.lean) | `[]` | 124 → 1109 / termStructural | True | True |
| [Equation1322_not_termStructuralFromFin_Equation124_projectionKernel2By17Scalars12489131516](../../equational_theories/Definability/Generated/ProjectionKernel2By17Scalars12489131516.lean) | `[]` | 124 → 1322 / termStructural | True | True |
| [Equation1728_not_termStructuralFromFin_Equation124_projectionKernel2By17Scalars12489131516](../../equational_theories/Definability/Generated/ProjectionKernel2By17Scalars12489131516.lean) | `[]` | 124 → 1728 / termStructural | True | True |
| [Equation3518_not_termStructuralFromFin_Equation1370_projectionKernel2By8Scalars1357](../../equational_theories/Definability/Generated/ProjectionKernel2By8Scalars1357.lean) | `[]` | 1370 → 3518 / termStructural | True | True |
| [Equation3520_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13](../../equational_theories/Definability/Generated/ProjectionKernel3By4Scalars13.lean) | `[]` | 690 → 3520 / termStructural | True | True |
| [Equation3321_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13](../../equational_theories/Definability/Generated/ProjectionKernel3By4Scalars13.lean) | `[]` | 690 → 3321 / termStructural | True | True |
| [Equation3323_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13](../../equational_theories/Definability/Generated/ProjectionKernel3By4Scalars13.lean) | `[]` | 690 → 3323 / termStructural | True | True |
| [Equation3523_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13](../../equational_theories/Definability/Generated/ProjectionKernel3By4Scalars13.lean) | `[]` | 690 → 3523 / termStructural | True | True |
| [Equation3524_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13](../../equational_theories/Definability/Generated/ProjectionKernel3By4Scalars13.lean) | `[]` | 690 → 3524 / termStructural | True | True |
| [Equation3464_not_termStructuralFromFin_Equation58_projectionKernel3By5Scalars1234](../../equational_theories/Definability/Generated/ProjectionKernel3By5Scalars1234.lean) | `[]` | 58 → 3464 / termStructural | True | True |
| [Equation3464_not_termStructuralFromFin_Equation1437_projectionKernel3By5Scalars1234](../../equational_theories/Definability/Generated/ProjectionKernel3By5Scalars1234.lean) | `[]` | 1437 → 3464 / termStructural | True | True |
| [Equation3258_not_termStructuralFromFin_Equation58_projectionKernel3By5Scalars1234](../../equational_theories/Definability/Generated/ProjectionKernel3By5Scalars1234.lean) | `[]` | 58 → 3258 / termStructural | True | True |
| [Equation3258_not_termStructuralFromFin_Equation1437_projectionKernel3By5Scalars1234](../../equational_theories/Definability/Generated/ProjectionKernel3By5Scalars1234.lean) | `[]` | 1437 → 3258 / termStructural | True | True |
| [Equation4284_not_termStructuralFromFin_Equation58_projectionKernel3By7Scalars123456](../../equational_theories/Definability/Generated/ProjectionKernel3By7Scalars123456.lean) | `[]` | 58 → 4284 / termStructural | True | True |
| [Equation3258_not_termStructuralFromFin_Equation446_projectionKernel4By11Scalars12345678910](../../equational_theories/Definability/Generated/ProjectionKernel4By11Scalars12345678910.lean) | `[]` | 446 → 3258 / termStructural | True | True |
| [Equation4275_not_termStructuralFromFin_Equation690_projectionVector3By8Upper](../../equational_theories/Definability/Generated/ProjectionVector3By8Upper.lean) | `[]` | 690 → 4275 / termStructural | True | True |
| [Equation1250_not_termStructuralFromFin_Equation1255_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 3)']` | 1255 → 1250 / termStructural | True | True |
| [Equation100_not_termStructuralFromFin_Equation1253_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 4)']` | 1253 → 100 / termStructural | True | True |
| [Equation1250_not_termStructuralFromFin_Equation1240_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 2)']` | 1240 → 1250 / termStructural | True | True |
| [Equation846_not_termStructuralFromFin_Equation1049_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 2)']` | 1049 → 846 / termStructural | True | True |
| [Equation1701_not_termStructuralFromFin_Equation626_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 3)']` | 626 → 1701 / termStructural | True | True |
| [Equation3320_not_termStructuralFromFin_Equation420_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 3)']` | 420 → 3320 / termStructural | True | True |
| [Equation1672_not_termStructuralFromFin_Equation1724_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 4)']` | 1724 → 1672 / termStructural | True | True |
| [Equation844_not_termStructuralFromFin_Equation1052_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FreeOrbit.A 2 2)']` | 1052 → 844 / termStructural | True | True |
| [Equation1731_not_termStructuralFromFin_Equation1049_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 3)']` | 1049 → 1731 / termStructural | True | True |
| [Equation1267_not_termStructuralFromFin_Equation1263_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 4)']` | 1263 → 1267 / termStructural | True | True |
| [Equation3462_not_termStructuralFromFin_Equation1435_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 4)']` | 1435 → 3462 / termStructural | True | True |
| [Equation1254_not_termStructuralFromFin_Equation1253_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 4)']` | 1253 → 1254 / termStructural | True | True |
| [Equation3457_not_termStructuralFromFin_Equation623_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 4)']` | 623 → 3457 / termStructural | True | True |
| [Equation1023_not_termStructuralFromFin_Equation50_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount0.lean) | `['(FixedPointCycle.A 4)']` | 50 → 1023 / termStructural | True | True |
| [Equation847_not_termStructuralFromFin_Equation1263_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 2)']` | 1263 → 847 / termStructural | True | True |
| [Equation1731_not_termStructuralFromFin_Equation440_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 3)']` | 440 → 1731 / termStructural | True | True |
| [Equation1255_not_termStructuralFromFin_Equation1263_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 2)']` | 1263 → 1255 / termStructural | True | True |
| [Equation818_not_termStructuralFromFin_Equation1224_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 2)']` | 1224 → 818 / termStructural | True | True |
| [Equation418_not_termStructuralFromFin_Equation626_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 3)']` | 626 → 418 / termStructural | True | True |
| [Equation3533_not_termStructuralFromFin_Equation420_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 3)']` | 420 → 3533 / termStructural | True | True |
| [Equation847_not_termStructuralFromFin_Equation1255_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 3)']` | 1255 → 847 / termStructural | True | True |
| [Equation1042_not_termStructuralFromFin_Equation1056_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 4)']` | 1056 → 1042 / termStructural | True | True |
| [Equation1250_not_termStructuralFromFin_Equation847_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FreeOrbit.A 2 2)']` | 847 → 1250 / termStructural | True | True |
| [Equation436_not_termStructuralFromFin_Equation1049_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 3)']` | 1049 → 436 / termStructural | True | True |
| [Equation422_not_termStructuralFromFin_Equation420_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 4)']` | 420 → 422 / termStructural | True | True |
| [Equation3462_not_termStructuralFromFin_Equation1638_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 4)']` | 1638 → 3462 / termStructural | True | True |
| [Equation3259_not_termStructuralFromFin_Equation1435_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 4)']` | 1435 → 3259 / termStructural | True | True |
| [Equation3457_not_termStructuralFromFin_Equation1435_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 4)']` | 1435 → 3457 / termStructural | True | True |
| [Equation1226_not_termStructuralFromFin_Equation1252_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount1.lean) | `['(FixedPointCycle.A 4)']` | 1252 → 1226 / termStructural | True | True |
| [Equation152_not_termStructuralFromFin_Equation626_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FixedPointCycle.A 3)']` | 626 → 152 / termStructural | True | True |
| [Equation3257_not_termStructuralFromFin_Equation420_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FixedPointCycle.A 4)']` | 420 → 3257 / termStructural | True | True |
| [Equation621_not_termStructuralFromFin_Equation626_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FixedPointCycle.A 3)']` | 626 → 621 / termStructural | True | True |
| [Equation1039_not_termStructuralFromFin_Equation1263_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FixedPointCycle.A 3)']` | 1263 → 1039 / termStructural | True | True |
| [Equation1635_not_termStructuralFromFin_Equation56_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FixedPointCycle.A 3)']` | 56 → 1635 / termStructural | True | True |
| [Equation3533_not_termStructuralFromFin_Equation626_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FixedPointCycle.A 4)']` | 626 → 3533 / termStructural | True | True |
| [Equation1250_not_termStructuralFromFin_Equation1263_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FreeOrbit.A 2 2)']` | 1263 → 1250 / termStructural | True | True |
| [Equation843_not_termStructuralFromFin_Equation847_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FreeOrbit.A 2 2)']` | 847 → 843 / termStructural | True | True |
| [Equation417_not_termStructuralFromFin_Equation420_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FixedPointCycle.A 4)']` | 420 → 417 / termStructural | True | True |
| [Equation1249_not_termStructuralFromFin_Equation1253_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FixedPointCycle.A 4)']` | 1253 → 1249 / termStructural | True | True |
| [Equation3259_not_termStructuralFromFin_Equation1638_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FixedPointCycle.A 4)']` | 1638 → 3259 / termStructural | True | True |
| [Equation3457_not_termStructuralFromFin_Equation1638_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount2.lean) | `['(FixedPointCycle.A 4)']` | 1638 → 3457 / termStructural | True | True |
| [Equation843_not_termStructuralFromFin_Equation1253_symmetryCount](../../equational_theories/Definability/Generated/SymmetryCount3.lean) | `['(FixedPointsOrbit.A (Fin 2)']` | 1253 → 843 / termStructural | True | True |
| [Equation1038_not_termStructuralFromFin_Equation477_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount0.lean) | `[]` | 477 → 1038 / termStructural | True | True |
| [Equation823_not_termStructuralFromFin_Equation861_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount0.lean) | `[]` | 861 → 823 / termStructural | True | True |
| [Equation1226_not_termStructuralFromFin_Equation861_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount0.lean) | `[]` | 861 → 1226 / termStructural | True | True |
| [Equation3472_not_termStructuralFromFin_Equation477_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount1.lean) | `[]` | 477 → 3472 / termStructural | True | True |
| [Equation3721_not_termStructuralFromFin_Equation861_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount2.lean) | `[]` | 861 → 3721 / termStructural | True | True |
| [Equation614_not_termStructuralFromFin_Equation1026_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount2.lean) | `[]` | 1026 → 614 / termStructural | True | True |
| [Equation817_not_termStructuralFromFin_Equation1026_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount2.lean) | `[]` | 1026 → 817 / termStructural | True | True |
| [Equation614_not_termStructuralFromFin_Equation1682_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount2.lean) | `[]` | 1682 → 614 / termStructural | True | True |
| [Equation817_not_termStructuralFromFin_Equation1682_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount2.lean) | `[]` | 1682 → 817 / termStructural | True | True |
| [Equation3712_not_termStructuralFromFin_Equation861_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount3.lean) | `[]` | 861 → 3712 / termStructural | True | True |
| [Equation835_not_termStructuralFromFin_Equation861_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount3.lean) | `[]` | 861 → 835 / termStructural | True | True |
| [Equation842_not_termStructuralFromFin_Equation861_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount3.lean) | `[]` | 861 → 842 / termStructural | True | True |
| [Equation3306_not_termStructuralFromFin_Equation500_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount4.lean) | `[]` | 500 → 3306 / termStructural | True | True |
| [Equation3261_not_termStructuralFromFin_Equation500_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount4.lean) | `[]` | 500 → 3261 / termStructural | True | True |
| [Equation3721_not_termStructuralFromFin_Equation56_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount5.lean) | `[]` | 56 → 3721 / termStructural | True | True |
| [Equation1434_not_termStructuralFromFin_Equation1525_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount6.lean) | `[]` | 1525 → 1434 / termStructural | True | True |
| [Equation1637_not_termStructuralFromFin_Equation56_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount7.lean) | `[]` | 56 → 1637 / termStructural | True | True |
| [Equation3712_not_termStructuralFromFin_Equation56_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount7.lean) | `[]` | 56 → 3712 / termStructural | True | True |
| [Equation3253_not_termStructuralFromFin_Equation75_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount7.lean) | `[]` | 75 → 3253 / termStructural | True | True |
| [Equation1637_not_termStructuralFromFin_Equation1638_truncatedCount](../../equational_theories/Definability/Generated/TruncatedCount8.lean) | `[]` | 1638 → 1637 / termStructural | True | True |
| [Equation63_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 63 / termDefinable | False | False |
| [Equation63_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 63 / termDefinable | False | False |
| [Equation73_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 73 / termDefinable | False | False |
| [Equation73_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 73 / termDefinable | False | False |
| [Equation118_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 118 / termDefinable | False | False |
| [Equation118_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 118 / termDefinable | False | False |
| [Equation125_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 125 / termDefinable | False | False |
| [Equation125_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 125 / termDefinable | False | False |
| [Equation222_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 222 / termDefinable | False | False |
| [Equation222_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 222 / termDefinable | False | False |
| [Equation229_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 229 / termDefinable | False | False |
| [Equation229_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 229 / termDefinable | False | False |
| [Equation271_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 271 / termDefinable | False | False |
| [Equation271_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 271 / termDefinable | False | False |
| [Equation274_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 274 / termDefinable | False | False |
| [Equation274_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 274 / termDefinable | False | False |
| [Equation467_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 467 / termDefinable | False | True |
| [Equation467_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 467 / termDefinable | False | True |
| [Equation504_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 504 / termDefinable | False | False |
| [Equation504_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 504 / termDefinable | False | False |
| [Equation667_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 667 / termDefinable | False | True |
| [Equation667_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 667 / termDefinable | False | True |
| [Equation870_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 870 / termDefinable | False | False |
| [Equation870_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 870 / termDefinable | False | False |
| [Equation910_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 910 / termDefinable | False | False |
| [Equation910_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 910 / termDefinable | False | False |
| [Equation917_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 917 / termDefinable | False | False |
| [Equation917_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 917 / termDefinable | False | False |
| [Equation1086_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 1086 / termDefinable | False | False |
| [Equation1086_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 1086 / termDefinable | False | False |
| [Equation1685_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 1685 / termDefinable | False | False |
| [Equation1685_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 1685 / termDefinable | False | False |
| [Equation1692_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 1692 / termDefinable | False | False |
| [Equation1692_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 1692 / termDefinable | False | False |
| [Equation1722_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 1722 / termDefinable | False | False |
| [Equation1722_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 1722 / termDefinable | False | False |
| [Equation1729_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 1729 / termDefinable | False | False |
| [Equation1729_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 1729 / termDefinable | False | False |
| [Equation1895_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 1895 / termDefinable | False | False |
| [Equation1895_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 1895 / termDefinable | False | False |
| [Equation1898_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 1898 / termDefinable | False | False |
| [Equation1898_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 1898 / termDefinable | False | False |
| [Equation1922_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 1922 / termDefinable | False | False |
| [Equation1922_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 1922 / termDefinable | False | False |
| [Equation1925_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 1925 / termDefinable | False | False |
| [Equation1925_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 1925 / termDefinable | False | False |
| [Equation2541_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 2541 / termDefinable | False | False |
| [Equation2541_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 2541 / termDefinable | False | False |
| [Equation2697_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 2697 / termDefinable | False | False |
| [Equation2697_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 2697 / termDefinable | False | False |
| [Equation2710_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 2710 / termDefinable | False | False |
| [Equation2710_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 2710 / termDefinable | False | False |
| [Equation2737_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 2737 / termDefinable | False | False |
| [Equation2737_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 2737 / termDefinable | False | False |
| [Equation2900_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 2900 / termDefinable | False | True |
| [Equation2900_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 2900 / termDefinable | False | True |
| [Equation3140_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3140 / termDefinable | False | True |
| [Equation3140_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3140 / termDefinable | False | True |
| [Equation3143_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3143 / termDefinable | False | False |
| [Equation3143_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3143 / termDefinable | False | False |
| [Equation3269_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3269 / termDefinable | False | False |
| [Equation3269_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3269 / termDefinable | False | False |
| [Equation3279_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3279 / termDefinable | False | False |
| [Equation3279_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3279 / termDefinable | False | False |
| [Equation3345_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3345 / termDefinable | False | False |
| [Equation3345_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3345 / termDefinable | False | False |
| [Equation3475_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3475 / termDefinable | False | False |
| [Equation3475_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3475 / termDefinable | False | False |
| [Equation3482_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3482 / termDefinable | False | False |
| [Equation3482_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3482 / termDefinable | False | False |
| [Equation3548_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3548 / termDefinable | False | False |
| [Equation3548_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3548 / termDefinable | False | False |
| [Equation3881_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3881 / termDefinable | False | False |
| [Equation3881_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3881 / termDefinable | False | False |
| [Equation3888_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3888 / termDefinable | False | False |
| [Equation3888_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3888 / termDefinable | False | False |
| [Equation3954_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 3954 / termDefinable | False | False |
| [Equation3954_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 3954 / termDefinable | False | False |
| [Equation4081_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 4081 / termDefinable | False | False |
| [Equation4081_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 4081 / termDefinable | False | False |
| [Equation4084_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 4084 / termDefinable | False | False |
| [Equation4084_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 4084 / termDefinable | False | False |
| [Equation4157_not_termDefinableFrom_Equation1516](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 1516 → 4157 / termDefinable | False | False |
| [Equation4157_not_termDefinableFrom_Equation2091](../../equational_theories/Definability/R1516Cover.lean) | `['R']` | 2091 → 4157 / termDefinable | False | False |
| [Equation40_not_definableFrom_Equation4364](../../equational_theories/Definability/Semilattice.lean) | `['NEFinsetInt']` | 4364 → 40 / definable | False | False |
| [Equation40_not_definableFrom_Equation4541](../../equational_theories/Definability/Semilattice.lean) | `['NEFinsetInt']` | 4541 → 40 / definable | False | False |
| [Equation14_not_structuralFromFin_Equation680](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 680 → 14 / structural | True | True |
| [Equation14_not_structuralFromFin_Equation692](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 692 → 14 / structural | True | True |
| [Equation14_not_structuralFromFin_Equation1276](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1276 → 14 / structural | True | True |
| [Equation14_not_structuralFromFin_Equation1695](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1695 → 14 / structural | True | True |
| [Equation14_not_structuralFromFin_Equation1719](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1719 → 14 / structural | True | True |
| [Equation1073_not_structuralFromFin_Equation680](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 680 → 1073 / structural | True | True |
| [Equation1073_not_structuralFromFin_Equation692](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 692 → 1073 / structural | True | True |
| [Equation1073_not_structuralFromFin_Equation1276](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1276 → 1073 / structural | True | True |
| [Equation1073_not_structuralFromFin_Equation1695](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1695 → 1073 / structural | True | True |
| [Equation1073_not_structuralFromFin_Equation1719](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1719 → 1073 / structural | True | True |
| [Equation4386_not_structuralFromFin_Equation680](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 680 → 4386 / structural | True | True |
| [Equation4386_not_structuralFromFin_Equation692](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 692 → 4386 / structural | True | True |
| [Equation4386_not_structuralFromFin_Equation1276](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1276 → 4386 / structural | True | True |
| [Equation4386_not_structuralFromFin_Equation1695](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1695 → 4386 / structural | True | True |
| [Equation4386_not_structuralFromFin_Equation1719](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1719 → 4386 / structural | True | True |
| [Equation4458_not_structuralFromFin_Equation680](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 680 → 4458 / structural | True | True |
| [Equation4458_not_structuralFromFin_Equation692](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 692 → 4458 / structural | True | True |
| [Equation4458_not_structuralFromFin_Equation1276](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1276 → 4458 / structural | True | True |
| [Equation4458_not_structuralFromFin_Equation1695](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1695 → 4458 / structural | True | True |
| [Equation4458_not_structuralFromFin_Equation1719](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1719 → 4458 / structural | True | True |
| [Equation1519_not_structuralFromFin_Equation1719](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1719 → 1519 / structural | True | True |
| [Equation3472_not_structuralFromFin_Equation1719](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1719 → 3472 / structural | True | True |
| [Equation3272_not_structuralFromFin_Equation1719](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1719 → 3272 / structural | True | True |
| [Equation310_not_structuralFromFin_Equation1488](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1488 → 310 / structural | True | True |
| [Equation3262_not_structuralFromFin_Equation1488](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1488 → 3262 / structural | True | True |
| [Equation3465_not_structuralFromFin_Equation1488](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1488 → 3465 / structural | True | True |
| [Equation3466_not_structuralFromFin_Equation1488](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1488 → 3466 / structural | True | True |
| [Equation4270_not_structuralFromFin_Equation1488](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1488 → 4270 / structural | True | True |
| [Equation4272_not_structuralFromFin_Equation1488](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1488 → 4272 / structural | True | True |
| [Equation3323_not_structuralFromFin_Equation1488](../../equational_theories/Definability/TransvectionE9.lean) | `[]` | 1488 → 3323 / structural | True | True |
| [Equation1489_not_termStructuralFromFin_Equation1516_twisted](../../equational_theories/Definability/TwistedRecovery.lean) | `['_']` | 1516 → 1489 / termStructural | True | True |
| [Equation1313_not_termStructuralFromFin_Equation1076_twisted](../../equational_theories/Definability/TwistedRecovery.lean) | `['_']` | 1076 → 1313 / termStructural | True | True |
| [Equation3548_not_termStructuralFromFin_Equation1685_twisted](../../equational_theories/Definability/TwistedRecovery.lean) | `['_']` | 1685 → 3548 / termStructural | True | True |
