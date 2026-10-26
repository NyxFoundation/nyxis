import type { Metadata } from "next";
import type { ReactNode } from "react";
import { AuthProvider, Header } from "../components/auth";
import { Zen_Kaku_Gothic_New, DM_Mono } from "next/font/google";
import "./globals.css";

const sans = Zen_Kaku_Gothic_New({ weight: ["400", "500", "700", "900"], subsets: ["latin"], variable: "--font-sans", display: "swap" });
const mono = DM_Mono({ weight: ["400", "500"], subsets: ["latin"], variable: "--font-mono", display: "swap" });

export const metadata: Metadata = { title: "Nyxis 掲示板", description: "Nyxis 公式サンプルの掲示板" };

export default function Layout({ children }: { children: ReactNode }) {
  return <html lang="ja"><body className={`${sans.variable} ${mono.variable}`}>
    <AuthProvider><Header />{children}</AuthProvider>
  </body></html>;
}
