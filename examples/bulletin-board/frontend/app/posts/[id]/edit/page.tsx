import { PostEdit } from "../../../../components/post-edit";
export default async function Page({ params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  return <PostEdit id={id} />;
}
